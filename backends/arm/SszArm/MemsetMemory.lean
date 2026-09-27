import SszArm.Memset

namespace SszArm.Memset

open BitVec

/-- The exact memory image after filling the first `k` bytes. -/
def image (m : Memory) (dst : BitVec 64) (value : BitVec 8) (k : Nat)
    (a : BitVec 64) : BitVec 8 :=
  if dst.toNat ≤ a.toNat ∧ a.toNat < dst.toNat + k then value else m a

/-- q0 is initialized only when the original length reaches the bulk threshold. -/
structure Invariant (initial : ArmState) (dst : BitVec 64) (value : BitVec 8)
    (n k : Nat) (s : ArmState) : Prop where
  bound : k ≤ n
  count : r (.GPR 2) s = BitVec.ofNat 64 (n - k)
  target : r (.GPR 3) s = dst + BitVec.ofNat 64 k
  value_reg : (r (.GPR 1) s).setWidth 8 = value
  fill : 16 ≤ n → r (.SFP 0) s = repeatedByte value
  memory : ∀ a, s.mem a = image initial.mem dst value k a

/-- Nonwrapping byte-level writes, without the model's native-SAT lemmas. -/
theorem memory_advance (initial s : ArmState) (dst : BitVec 64) (value : BitVec 8)
    (n k b : Nat) (hb : 0 < b) (hkb : k + b ≤ n)
    (hdst : dst.toNat + n ≤ 2 ^ 64) (data : BitVec (b * 8))
    (hdata : ∀ i, i < b → data.extractLsByte i = value)
    (hm : ∀ a, s.mem a = image initial.mem dst value k a) (a : BitVec 64) :
    (write_mem_bytes b (dst + BitVec.ofNat 64 k) data s).mem a =
      image initial.mem dst value (k + b) a := by
  have hdn : (dst + BitVec.ofNat 64 k).toNat = dst.toNat + k := by bv_omega
  have hspace : (dst + BitVec.ofNat 64 k).toNat + b ≤ 2 ^ 64 := by omega
  rw [Memory.write_mem_bytes_eq_mem_write_bytes]
  change s.mem.write_bytes b (dst + BitVec.ofNat 64 k) data a = _
  by_cases hlo : a.toNat < dst.toNat + k
  · rw [Memory.write_bytes_eq_of_le (by omega) hspace, hm]
    simp only [image]
    split <;> split <;> simp_all <;> omega
  · by_cases hhi : dst.toNat + k + b ≤ a.toNat
    · rw [Memory.write_bytes_eq_of_ge (by omega) hspace, hm]
      simp only [image]
      split <;> split <;> simp_all <;> omega
    · have hj : (a - (dst + BitVec.ofNat 64 k)).toNat =
          a.toNat - (dst.toNat + k) := by bv_omega
      have hjb : (a - (dst + BitVec.ofNat 64 k)).toNat < b := by omega
      rw [Memory.write_bytes_eq_extractLsByte (by omega) (by omega) hspace, hdata _ hjb]
      simp only [image, if_pos (by omega : dst.toNat ≤ a.toNat ∧ a.toNat < dst.toNat + (k + b))]

theorem invariant_advance_bulk (initial s : ArmState) (dst : BitVec 64)
    (value : BitVec 8) (n k : Nat) (hn : n < 2 ^ 64) (hkb : k + 16 ≤ n)
    (hdst : dst.toNat + n ≤ 2 ^ 64) (h : Invariant initial dst value n k s) :
    Invariant initial dst value n (k + 16) (bulk s) := by
  refine ⟨hkb, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(bulk_data s).2.1, h.count]
    bv_omega
  · rw [(bulk_data s).2.2.1, h.target]
    bv_omega
  · rw [bulk_frame s (.GPR 1) (by simp [Preserved])]
    exact h.value_reg
  · intro hlarge
    rw [(bulk_data s).2.2.2]
    exact h.fill hlarge
  · intro a
    rw [(bulk_data s).1, h.target, h.fill (by omega)]
    exact memory_advance initial s dst value n k 16 (by decide) hkb hdst
      (repeatedByte value) (fun i hi => repeatedByte_extract value i hi) h.memory a

theorem invariant_advance_byte (initial s : ArmState) (dst : BitVec 64)
    (value : BitVec 8) (n k : Nat) (hkb : k + 1 ≤ n)
    (hdst : dst.toNat + n ≤ 2 ^ 64) (h : Invariant initial dst value n k s) :
    Invariant initial dst value n (k + 1) (byte s) := by
  refine ⟨hkb, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(byte_data s).2.1, h.count]
    bv_omega
  · rw [(byte_data s).2.2.1, h.target]
    bv_omega
  · rw [byte_frame s (.GPR 1) (by simp [Preserved])]
    exact h.value_reg
  · intro hlarge
    rw [(byte_data s).2.2.2]
    exact h.fill hlarge
  · intro a
    rw [(byte_data s).1, h.target, h.value_reg]
    apply memory_advance initial s dst value n k 1 (by decide) hkb hdst value ?_ h.memory a
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simp [BitVec.extractLsByte, bitvec_rules]

private theorem invariant_iterate (initial : ArmState) (dst : BitVec 64)
    (value : BitVec 8) (n b : Nat) (f : ArmState → ArmState)
    (advance : ∀ s k, k + b ≤ n → Invariant initial dst value n k s →
      Invariant initial dst value n (k + b) (f s))
    (s : ArmState) (k q : Nat) (hbound : k + b * q ≤ n)
    (h : Invariant initial dst value n k s) :
    Invariant initial dst value n (k + b * q) (iterate f q s) := by
  induction q generalizing s k with
  | zero => simpa only [iterate, Nat.mul_zero, Nat.add_zero] using h
  | succ q ih =>
    simp only [Nat.mul_succ] at hbound
    have hs := advance s k (by omega) h
    have ht := ih (s := f s) (k := k + b) (by omega) hs
    have hindex : k + b + b * q = k + b * (q + 1) := by
      rw [Nat.mul_succ]
      omega
    simpa only [iterate, hindex] using ht

theorem invariant_bulk (initial s : ArmState) (dst : BitVec 64)
    (value : BitVec 8) (n k q : Nat) (hn : n < 2 ^ 64) (hbound : k + 16 * q ≤ n)
    (hdst : dst.toNat + n ≤ 2 ^ 64) (h : Invariant initial dst value n k s) :
    Invariant initial dst value n (k + 16 * q) (iterate bulk q s) := by
  refine invariant_iterate initial dst value n 16 bulk ?_ s k q hbound h
  intro u j hj hu
  exact invariant_advance_bulk initial u dst value n j hn hj hdst hu

theorem invariant_byte (initial s : ArmState) (dst : BitVec 64)
    (value : BitVec 8) (n k t : Nat) (hbound : k + t ≤ n)
    (hdst : dst.toNat + n ≤ 2 ^ 64) (h : Invariant initial dst value n k s) :
    Invariant initial dst value n (k + t) (iterate byte t s) := by
  have advance : ∀ u j, j + 1 ≤ n → Invariant initial dst value n j u →
      Invariant initial dst value n (j + 1) (byte u) := by
    intro u j hj hu
    exact invariant_advance_byte initial u dst value n j hj hdst hu
  simpa only [Nat.one_mul] using invariant_iterate initial dst value n 1 byte
    advance s k t (by simpa only [Nat.one_mul] using hbound) h

/-- Exact fill and unchanged memory outside the destination, for arbitrary length. -/
theorem result_memory (s : ArmState)
    (hdst : (r (.GPR 0) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64) :
    ∀ a, (result s).mem a = image s.mem (r (.GPR 0) s)
      ((r (.GPR 1) s).setWidth 8) (r (.GPR 2) s).toNat a := by
  let n := (r (.GPR 2) s).toNat
  let dst := r (.GPR 0) s
  let value := (r (.GPR 1) s).setWidth 8
  have hn : n < 2 ^ 64 := by dsimp [n]; bv_omega
  obtain ⟨hm, h1, h2, h3, hfill⟩ := prefix_state_data s
  have hstart : Invariant s dst value n 0 (prefix_state s) := by
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [n] using h2
    · simpa [dst] using h3
    · simpa [value] using congrArg (BitVec.setWidth 8) h1
    · exact hfill
    · intro a
      simp only [hm, image, Nat.add_zero]
      rw [if_neg (by omega)]
  have hbulk := invariant_bulk s (prefix_state s) dst value n 0 (n / 16) hn
    (by omega) hdst hstart
  have htest : Invariant s dst value n (16 * (n / 16))
      (instruction 8 (iterate bulk (n / 16) (prefix_state s))) := by
    refine ⟨by simpa only [Nat.zero_add] using hbulk.bound, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [instruction, state_simp_rules] using hbulk.count
    · simpa [instruction, state_simp_rules] using hbulk.target
    · simpa [instruction, state_simp_rules] using hbulk.value_reg
    · intro hlarge
      simpa [instruction, state_simp_rules] using hbulk.fill hlarge
    · intro a
      simpa [instruction, state_simp_rules] using hbulk.memory a
  have htail := invariant_byte s (instruction 8 (iterate bulk (n / 16) (prefix_state s)))
    dst value n (16 * (n / 16)) (n % 16) (by omega) hdst htest
  have htotal : 16 * (n / 16) + n % 16 = n := by omega
  intro a
  simpa only [result, instruction, ArmState.mem_w_eq_mem, htotal] using htail.memory a

/-- Every destination byte is exactly the low eight bits of the original x1. -/
theorem result_byte (s : ArmState)
    (hdst : (r (.GPR 0) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64)
    (i : Nat) (hi : i < (r (.GPR 2) s).toNat) :
    (result s).mem (r (.GPR 0) s + BitVec.ofNat 64 i) = (r (.GPR 1) s).setWidth 8 := by
  rw [result_memory s hdst]
  have ha : (r (.GPR 0) s + BitVec.ofNat 64 i).toNat = (r (.GPR 0) s).toNat + i := by
    bv_omega
  simp only [image, ha]
  rw [if_pos (by omega)]

end SszArm.Memset

import SszArm.Memcpy

namespace SszArm.Memcpy

open BitVec

/-- The exact memory image after copying the first `k` bytes. -/
def image (m : Memory) (dst src : BitVec 64) (k : Nat) (a : BitVec 64) : BitVec 8 :=
  if dst.toNat ≤ a.toNat ∧ a.toNat < dst.toNat + k
  then m (src + BitVec.ofNat 64 (a.toNat - dst.toNat)) else m a

/-- Natural-address disjointness permits touching endpoints but not overlap. -/
def Disjoint (dst src : BitVec 64) (n : Nat) : Prop :=
  dst.toNat + n ≤ src.toNat ∨ src.toNat + n ≤ dst.toNat

/-- Loop invariant, retaining the original arbitrary memory as the specification. -/
structure Invariant (initial : ArmState) (dst src : BitVec 64)
    (n k : Nat) (s : ArmState) : Prop where
  bound : k ≤ n
  source : r (.GPR 1) s = src + BitVec.ofNat 64 k
  count : r (.GPR 2) s = BitVec.ofNat 64 (n - k)
  target : r (.GPR 3) s = dst + BitVec.ofNat 64 k
  memory : ∀ a, s.mem a = image initial.mem dst src k a

/-- Byte-level read/write reasoning; none of the native-SAT separation lemmas
from the model are used. -/
theorem memory_advance (initial s : ArmState) (dst src : BitVec 64)
    (n k b : Nat) (hb : 0 < b) (hkb : k + b ≤ n)
    (hdst : dst.toNat + n ≤ 2 ^ 64) (hsrc : src.toNat + n ≤ 2 ^ 64)
    (hsep : Disjoint dst src n)
    (hm : ∀ a, s.mem a = image initial.mem dst src k a) (a : BitVec 64) :
    (write_mem_bytes b (dst + BitVec.ofNat 64 k)
      (read_mem_bytes b (src + BitVec.ofNat 64 k) s) s).mem a =
        image initial.mem dst src (k + b) a := by
  have hdn : (dst + BitVec.ofNat 64 k).toNat = dst.toNat + k := by bv_omega
  have hsn : (src + BitVec.ofNat 64 k).toNat = src.toNat + k := by bv_omega
  have hdspace : (dst + BitVec.ofNat 64 k).toNat + b ≤ 2 ^ 64 := by omega
  have hsspace : (src + BitVec.ofNat 64 k).toNat + b ≤ 2 ^ 64 := by omega
  rw [Memory.write_mem_bytes_eq_mem_write_bytes,
    Memory.State.read_mem_bytes_eq_mem_read_bytes]
  change s.mem.write_bytes b (dst + BitVec.ofNat 64 k)
    (s.mem.read_bytes b (src + BitVec.ofNat 64 k)) a = _
  by_cases hlo : a.toNat < dst.toNat + k
  · rw [Memory.write_bytes_eq_of_le (by omega) hdspace, hm]
    simp only [image]
    split <;> split <;> simp_all <;> omega
  · by_cases hhi : dst.toNat + k + b ≤ a.toNat
    · rw [Memory.write_bytes_eq_of_ge (by omega) hdspace, hm]
      simp only [image]
      split <;> split <;> simp_all <;> omega
    · have hj : (a - (dst + BitVec.ofNat 64 k)).toNat = a.toNat - (dst.toNat + k) := by
        bv_omega
      have hjb : (a - (dst + BitVec.ofNat 64 k)).toNat < b := by omega
      rw [Memory.write_bytes_eq_extractLsByte (by omega) (by omega) hdspace,
        Memory.extractLsByte_read_bytes hsspace, if_pos hjb]
      change s.mem (src + BitVec.ofNat 64 k +
        BitVec.ofNat 64 (a - (dst + BitVec.ofNat 64 k)).toNat) = _
      have hread : (src + BitVec.ofNat 64 k +
          BitVec.ofNat 64 (a - (dst + BitVec.ofNat 64 k)).toNat).toNat =
          src.toNat + k + (a - (dst + BitVec.ofNat 64 k)).toNat := by bv_omega
      have hout : ¬(dst.toNat ≤ (src + BitVec.ofNat 64 k +
          BitVec.ofNat 64 (a - (dst + BitVec.ofNat 64 k)).toNat).toNat ∧
          (src + BitVec.ofNat 64 k +
          BitVec.ofNat 64 (a - (dst + BitVec.ofNat 64 k)).toNat).toNat < dst.toNat + k) := by
        rcases hsep with hsep | hsep <;> omega
      have hin : dst.toNat ≤ a.toNat ∧ a.toNat < dst.toNat + (k + b) := by omega
      rw [hm]
      simp only [image, if_neg hout, if_pos hin]
      congr 1
      bv_omega

theorem invariant_advance (initial s s' : ArmState) (dst src : BitVec 64)
    (n k b : Nat) (hn : n < 2 ^ 64) (hb : 0 < b) (hkb : k + b ≤ n)
    (hdst : dst.toNat + n ≤ 2 ^ 64) (hsrc : src.toNat + n ≤ 2 ^ 64)
    (hsep : Disjoint dst src n) (h : Invariant initial dst src n k s)
    (hmem : s'.mem = (write_mem_bytes b (r (.GPR 3) s)
      (read_mem_bytes b (r (.GPR 1) s) s) s).mem)
    (h1 : r (.GPR 1) s' = r (.GPR 1) s + BitVec.ofNat 64 b)
    (h2 : r (.GPR 2) s' = r (.GPR 2) s - BitVec.ofNat 64 b)
    (h3 : r (.GPR 3) s' = r (.GPR 3) s + BitVec.ofNat 64 b) :
    Invariant initial dst src n (k + b) s' := by
  refine ⟨hkb, ?_, ?_, ?_, ?_⟩
  · rw [h1, h.source]; bv_omega
  · rw [h2, h.count]; bv_omega
  · rw [h3, h.target]; bv_omega
  · intro a
    rw [hmem, h.target, h.source]
    exact memory_advance initial s dst src n k b hb hkb hdst hsrc hsep h.memory a

private theorem invariant_iterate (initial : ArmState) (dst src : BitVec 64)
    (n b : Nat) (f : ArmState → ArmState)
    (advance : ∀ s k, k + b ≤ n → Invariant initial dst src n k s →
      Invariant initial dst src n (k + b) (f s))
    (s : ArmState) (k q : Nat) (hbound : k + b * q ≤ n)
    (h : Invariant initial dst src n k s) :
    Invariant initial dst src n (k + b * q) (iterate f q s) := by
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

theorem invariant_bulk (initial s : ArmState) (dst src : BitVec 64)
    (n k q : Nat) (hn : n < 2 ^ 64) (hbound : k + 16 * q ≤ n)
    (hdst : dst.toNat + n ≤ 2 ^ 64) (hsrc : src.toNat + n ≤ 2 ^ 64)
    (hsep : Disjoint dst src n) (h : Invariant initial dst src n k s) :
    Invariant initial dst src n (k + 16 * q) (iterate bulk q s) := by
  refine invariant_iterate initial dst src n 16 bulk ?_ s k q hbound h
  intro t j hj ht
  exact invariant_advance initial t (bulk t) dst src n j 16 hn (by decide)
    hj hdst hsrc hsep ht (bulk_data t).1 (bulk_data t).2.1
    (bulk_data t).2.2.1 (bulk_data t).2.2.2

theorem invariant_byte (initial s : ArmState) (dst src : BitVec 64)
    (n k t : Nat) (hn : n < 2 ^ 64) (hbound : k + t ≤ n)
    (hdst : dst.toNat + n ≤ 2 ^ 64) (hsrc : src.toNat + n ≤ 2 ^ 64)
    (hsep : Disjoint dst src n) (h : Invariant initial dst src n k s) :
    Invariant initial dst src n (k + t) (iterate byte t s) := by
  have advance : ∀ t j, j + 1 ≤ n → Invariant initial dst src n j t →
      Invariant initial dst src n (j + 1) (byte t) := by
    intro t j hj ht
    exact invariant_advance initial t (byte t) dst src n j 1 hn (by decide)
      hj hdst hsrc hsep ht (byte_data t).1 (byte_data t).2.1
      (byte_data t).2.2.1 (byte_data t).2.2.2
  simpa only [Nat.one_mul] using invariant_iterate initial dst src n 1 byte
    advance s k t (by simpa only [Nat.one_mul] using hbound) h

/-- The algorithm copies arbitrary bytes and changes precisely the destination
region. This theorem is subsequently connected to `run` by `program_run`. -/
theorem result_memory (s : ArmState)
    (hdst : (r (.GPR 0) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64)
    (hsrc : (r (.GPR 1) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64)
    (hsep : Disjoint (r (.GPR 0) s) (r (.GPR 1) s) (r (.GPR 2) s).toNat) :
    ∀ a, (result s).mem a = image s.mem (r (.GPR 0) s) (r (.GPR 1) s)
      (r (.GPR 2) s).toNat a := by
  let n := (r (.GPR 2) s).toNat
  let dst := r (.GPR 0) s
  let src := r (.GPR 1) s
  have hn : n < 2 ^ 64 := by dsimp [n]; bv_omega
  obtain ⟨hm, h1, h2, h3⟩ := prefix_state_data s
  have hstart : Invariant s dst src n 0 (prefix_state s) := by
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · simpa [src] using h1
    · simpa [n] using h2
    · simpa [dst] using h3
    · intro a
      simp only [hm, image, Nat.add_zero]
      rw [if_neg (by omega)]
  have hbulk := invariant_bulk s (prefix_state s) dst src n 0 (n / 16) hn
    (by omega) hdst hsrc hsep hstart
  have htest : Invariant s dst src n (16 * (n / 16))
      (instruction 8 (iterate bulk (n / 16) (prefix_state s))) := by
    refine ⟨by simpa only [Nat.zero_add] using hbulk.bound, ?_, ?_, ?_, ?_⟩
    · simpa [instruction, state_simp_rules] using hbulk.source
    · simpa [instruction, state_simp_rules] using hbulk.count
    · simpa [instruction, state_simp_rules] using hbulk.target
    · intro a
      simpa [instruction, state_simp_rules] using hbulk.memory a
  have htail := invariant_byte s (instruction 8 (iterate bulk (n / 16) (prefix_state s)))
    dst src n (16 * (n / 16)) (n % 16) hn (by omega) hdst hsrc hsep htest
  have htotal : 16 * (n / 16) + n % 16 = n := by omega
  intro a
  simpa only [result, instruction, ArmState.mem_w_eq_mem, htotal] using htail.memory a

/-- A pointwise byte contract, including the caller's original source memory. -/
theorem result_byte (s : ArmState)
    (hdst : (r (.GPR 0) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64)
    (hsrc : (r (.GPR 1) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64)
    (hsep : Disjoint (r (.GPR 0) s) (r (.GPR 1) s) (r (.GPR 2) s).toNat)
    (i : Nat) (hi : i < (r (.GPR 2) s).toNat) :
    (result s).mem (r (.GPR 0) s + BitVec.ofNat 64 i) =
      s.mem (r (.GPR 1) s + BitVec.ofNat 64 i) := by
  rw [result_memory s hdst hsrc hsep]
  have ha : (r (.GPR 0) s + BitVec.ofNat 64 i).toNat = (r (.GPR 0) s).toNat + i := by
    bv_omega
  simp only [image, ha]
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

end SszArm.Memcpy


import SszArm.MemmoveBackwardProofs

namespace SszArm.Memmove

open BitVec

/-- The final image always reads the caller's original source snapshot. -/
abbrev image := SszArm.Memcpy.image

namespace Forward

open SszArm.Memcpy

/-- Byte-level read/write reasoning; none of the native-SAT separation lemmas
from the model are used. -/
theorem memory_advance (initial s : ArmState) (dst src : BitVec 64)
    (n k b : Nat) (hb : 0 < b) (hkb : k + b ≤ n)
    (hdst : dst.toNat + n ≤ 2 ^ 64) (hsrc : src.toNat + n ≤ 2 ^ 64)
    (horder : dst.toNat ≤ src.toNat)
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
    simp only [image, SszArm.Memcpy.image]
    split <;> split <;> simp_all <;> omega
  · by_cases hhi : dst.toNat + k + b ≤ a.toNat
    · rw [Memory.write_bytes_eq_of_ge (by omega) hdspace, hm]
      simp only [image, SszArm.Memcpy.image]
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
        omega
      have hin : dst.toNat ≤ a.toNat ∧ a.toNat < dst.toNat + (k + b) := by omega
      rw [hm]
      simp only [image, SszArm.Memcpy.image, if_neg hout, if_pos hin]
      congr 1
      bv_omega

theorem invariant_advance (initial s s' : ArmState) (dst src : BitVec 64)
    (n k b : Nat) (hn : n < 2 ^ 64) (hb : 0 < b) (hkb : k + b ≤ n)
    (hdst : dst.toNat + n ≤ 2 ^ 64) (hsrc : src.toNat + n ≤ 2 ^ 64)
    (horder : dst.toNat ≤ src.toNat) (h : Invariant initial dst src n k s)
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
    exact memory_advance initial s dst src n k b hb hkb hdst hsrc horder h.memory a

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
    (horder : dst.toNat ≤ src.toNat) (h : Invariant initial dst src n k s) :
    Invariant initial dst src n (k + 16 * q) (iterate bulk q s) := by
  refine invariant_iterate initial dst src n 16 bulk ?_ s k q hbound h
  intro t j hj ht
  exact invariant_advance initial t (bulk t) dst src n j 16 hn (by decide)
    hj hdst hsrc horder ht (bulk_data t).1 (bulk_data t).2.1
    (bulk_data t).2.2.1 (bulk_data t).2.2.2

theorem invariant_byte (initial s : ArmState) (dst src : BitVec 64)
    (n k t : Nat) (hn : n < 2 ^ 64) (hbound : k + t ≤ n)
    (hdst : dst.toNat + n ≤ 2 ^ 64) (hsrc : src.toNat + n ≤ 2 ^ 64)
    (horder : dst.toNat ≤ src.toNat) (h : Invariant initial dst src n k s) :
    Invariant initial dst src n (k + t) (iterate byte t s) := by
  have advance : ∀ t j, j + 1 ≤ n → Invariant initial dst src n j t →
      Invariant initial dst src n (j + 1) (byte t) := by
    intro t j hj ht
    exact invariant_advance initial t (byte t) dst src n j 1 hn (by decide)
      hj hdst hsrc horder ht (byte_data t).1 (byte_data t).2.1
      (byte_data t).2.2.1 (byte_data t).2.2.2
  simpa only [Nat.one_mul] using invariant_iterate initial dst src n 1 byte
    advance s k t (by simpa only [Nat.one_mul] using hbound) h

/-- The forward algorithm copies arbitrary bytes, permitting overlap, and changes precisely the destination
region. This theorem is subsequently connected to `run` by `program_run`. -/
theorem result_memory (s : ArmState)
    (hdst : (r (.GPR 0) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64)
    (hsrc : (r (.GPR 1) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64)
    (horder : (r (.GPR 0) s).toNat ≤ (r (.GPR 1) s).toNat) :
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
      simp only [hm, SszArm.Memcpy.image, Nat.add_zero]
      rw [if_neg (by omega)]
  have hbulk := invariant_bulk s (prefix_state s) dst src n 0 (n / 16) hn
    (by omega) hdst hsrc horder hstart
  have htest : Invariant s dst src n (16 * (n / 16))
      (instruction 8 (iterate bulk (n / 16) (prefix_state s))) := by
    refine ⟨by simpa only [Nat.zero_add] using hbulk.bound, ?_, ?_, ?_, ?_⟩
    · simpa [instruction, state_simp_rules] using hbulk.source
    · simpa [instruction, state_simp_rules] using hbulk.count
    · simpa [instruction, state_simp_rules] using hbulk.target
    · intro a
      simpa [instruction, state_simp_rules] using hbulk.memory a
  have htail := invariant_byte s (instruction 8 (iterate bulk (n / 16) (prefix_state s)))
    dst src n (16 * (n / 16)) (n % 16) hn (by omega) hdst hsrc horder htest
  have htotal : 16 * (n / 16) + n % 16 = n := by omega
  intro a
  simpa only [result, instruction, ArmState.mem_w_eq_mem, htotal] using htail.memory a

/-- A pointwise byte contract, including the caller's original source memory. -/
theorem result_byte (s : ArmState)
    (hdst : (r (.GPR 0) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64)
    (hsrc : (r (.GPR 1) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64)
    (horder : (r (.GPR 0) s).toNat ≤ (r (.GPR 1) s).toNat)
    (i : Nat) (hi : i < (r (.GPR 2) s).toNat) :
    (result s).mem (r (.GPR 0) s + BitVec.ofNat 64 i) =
      s.mem (r (.GPR 1) s + BitVec.ofNat 64 i) := by
  rw [result_memory s hdst hsrc horder]
  have ha : (r (.GPR 0) s + BitVec.ofNat 64 i).toNat = (r (.GPR 0) s).toNat + i := by
    bv_omega
  simp only [image, SszArm.Memcpy.image, ha]
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

end Forward

/-- Exact image after the last `k` bytes have been copied, from original memory. -/
def backwardImage (m : Memory) (dst src : BitVec 64) (n k : Nat)
    (a : BitVec 64) : BitVec 8 :=
  if dst.toNat + (n - k) ≤ a.toNat ∧ a.toNat < dst.toNat + n
  then m (src + BitVec.ofNat 64 (a.toNat - dst.toNat)) else m a

namespace Backward

private theorem sub16_add15 (p : BitVec 64) :
    p - 16#64 + 15#64 = p - 1#64 := by
  bv_omega

/-- `b` is the offset from the uncopied endpoint to the next access. The
subtraction stays modular so post-index updates may underflow after the last
chunk without changing the copied-memory invariant. -/
structure Invariant (initial : ArmState) (dst src : BitVec 64)
    (n k b : Nat) (s : ArmState) : Prop where
  bound : k ≤ n
  source : r (.GPR 1) s = src + BitVec.ofNat 64 (n - k) - BitVec.ofNat 64 b
  count : r (.GPR 2) s = BitVec.ofNat 64 (n - k)
  target : r (.GPR 3) s = dst + BitVec.ofNat 64 (n - k) - BitVec.ofNat 64 b
  memory : ∀ a, s.mem a = backwardImage initial.mem dst src n k a

/-- Earlier source bytes precede all earlier backward writes. The entire next
chunk is read before any write, so no separation within that chunk is needed. -/
theorem memory_advance (initial s : ArmState) (dst src : BitVec 64)
    (n k b : Nat) (hb : 0 < b) (hkb : k + b ≤ n)
    (hdst : dst.toNat + n ≤ 2 ^ 64) (_hsrc : src.toNat + n ≤ 2 ^ 64)
    (horder : src.toNat ≤ dst.toNat)
    (hm : ∀ a, s.mem a = backwardImage initial.mem dst src n k a) (a : BitVec 64) :
    (write_mem_bytes b (dst + BitVec.ofNat 64 (n - (k + b)))
      (read_mem_bytes b (src + BitVec.ofNat 64 (n - (k + b))) s) s).mem a =
        backwardImage initial.mem dst src n (k + b) a := by
  have hdn : (dst + BitVec.ofNat 64 (n - (k + b))).toNat =
      dst.toNat + (n - (k + b)) := by bv_omega
  have hsn : (src + BitVec.ofNat 64 (n - (k + b))).toNat =
      src.toNat + (n - (k + b)) := by bv_omega
  have hdspace : (dst + BitVec.ofNat 64 (n - (k + b))).toNat + b ≤ 2 ^ 64 := by omega
  have hsspace : (src + BitVec.ofNat 64 (n - (k + b))).toNat + b ≤ 2 ^ 64 := by omega
  rw [Memory.write_mem_bytes_eq_mem_write_bytes,
    Memory.State.read_mem_bytes_eq_mem_read_bytes]
  change s.mem.write_bytes b (dst + BitVec.ofNat 64 (n - (k + b)))
    (s.mem.read_bytes b (src + BitVec.ofNat 64 (n - (k + b)))) a = _
  by_cases hlo : a.toNat < dst.toNat + (n - (k + b))
  · rw [Memory.write_bytes_eq_of_le (by omega) hdspace, hm]
    simp only [backwardImage]
    split <;> split <;> simp_all <;> omega
  · by_cases hhi : dst.toNat + (n - k) ≤ a.toNat
    · rw [Memory.write_bytes_eq_of_ge (by omega) hdspace, hm]
      simp only [backwardImage]
      split <;> split <;> simp_all <;> omega
    · have hj : (a - (dst + BitVec.ofNat 64 (n - (k + b)))).toNat =
          a.toNat - (dst.toNat + (n - (k + b))) := by bv_omega
      have hjb : (a - (dst + BitVec.ofNat 64 (n - (k + b)))).toNat < b := by omega
      rw [Memory.write_bytes_eq_extractLsByte (by omega) (by omega) hdspace,
        Memory.extractLsByte_read_bytes hsspace, if_pos hjb]
      change s.mem (src + BitVec.ofNat 64 (n - (k + b)) +
        BitVec.ofNat 64 (a - (dst + BitVec.ofNat 64 (n - (k + b)))).toNat) = _
      have hread : (src + BitVec.ofNat 64 (n - (k + b)) +
          BitVec.ofNat 64 (a - (dst + BitVec.ofNat 64 (n - (k + b)))).toNat).toNat =
          src.toNat + (n - (k + b)) +
            (a - (dst + BitVec.ofNat 64 (n - (k + b)))).toNat := by bv_omega
      have hout : ¬(dst.toNat + (n - k) ≤
          (src + BitVec.ofNat 64 (n - (k + b)) +
            BitVec.ofNat 64 (a - (dst + BitVec.ofNat 64 (n - (k + b)))).toNat).toNat ∧
          (src + BitVec.ofNat 64 (n - (k + b)) +
            BitVec.ofNat 64 (a - (dst + BitVec.ofNat 64 (n - (k + b)))).toNat).toNat <
              dst.toNat + n) := by omega
      have hin : dst.toNat + (n - (k + b)) ≤ a.toNat ∧ a.toNat < dst.toNat + n := by omega
      rw [hm]
      simp only [backwardImage, if_neg hout, if_pos hin]
      congr 1
      bv_omega

theorem invariant_advance (initial s s' : ArmState) (dst src : BitVec 64)
    (n k b : Nat) (_hn : n < 2 ^ 64) (hb : 0 < b) (hkb : k + b ≤ n)
    (hdst : dst.toNat + n ≤ 2 ^ 64) (hsrc : src.toNat + n ≤ 2 ^ 64)
    (horder : src.toNat ≤ dst.toNat) (h : Invariant initial dst src n k b s)
    (hmem : s'.mem = (write_mem_bytes b (r (.GPR 3) s)
      (read_mem_bytes b (r (.GPR 1) s) s) s).mem)
    (h1 : r (.GPR 1) s' = r (.GPR 1) s - BitVec.ofNat 64 b)
    (h2 : r (.GPR 2) s' = r (.GPR 2) s - BitVec.ofNat 64 b)
    (h3 : r (.GPR 3) s' = r (.GPR 3) s - BitVec.ofNat 64 b) :
    Invariant initial dst src n (k + b) b s' := by
  have hd : dst + BitVec.ofNat 64 (n - k) - BitVec.ofNat 64 b =
      dst + BitVec.ofNat 64 (n - (k + b)) := by bv_omega
  have hs : src + BitVec.ofNat 64 (n - k) - BitVec.ofNat 64 b =
      src + BitVec.ofNat 64 (n - (k + b)) := by bv_omega
  refine ⟨hkb, ?_, ?_, ?_, ?_⟩
  · rw [h1, h.source, hs]
  · rw [h2, h.count]; bv_omega
  · rw [h3, h.target, hd]
  · intro a
    rw [hmem, h.target, h.source, hd, hs]
    exact memory_advance initial s dst src n k b hb hkb hdst hsrc horder h.memory a

private theorem invariant_iterate (initial : ArmState) (dst src : BitVec 64)
    (n b : Nat) (f : ArmState → ArmState)
    (advance : ∀ s k, k + b ≤ n → Invariant initial dst src n k b s →
      Invariant initial dst src n (k + b) b (f s))
    (s : ArmState) (k q : Nat) (hbound : k + b * q ≤ n)
    (h : Invariant initial dst src n k b s) :
    Invariant initial dst src n (k + b * q) b (iterate f q s) := by
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
    (horder : src.toNat ≤ dst.toNat) (h : Invariant initial dst src n k 16 s) :
    Invariant initial dst src n (k + 16 * q) 16 (iterate bulk q s) := by
  refine invariant_iterate initial dst src n 16 bulk ?_ s k q hbound h
  intro t j hj ht
  exact invariant_advance initial t (bulk t) dst src n j 16 hn (by decide)
    hj hdst hsrc horder ht (bulk_data t).1 (bulk_data t).2.1
    (bulk_data t).2.2.1 (bulk_data t).2.2.2

theorem invariant_byte (initial s : ArmState) (dst src : BitVec 64)
    (n k t : Nat) (hn : n < 2 ^ 64) (hbound : k + t ≤ n)
    (hdst : dst.toNat + n ≤ 2 ^ 64) (hsrc : src.toNat + n ≤ 2 ^ 64)
    (horder : src.toNat ≤ dst.toNat) (h : Invariant initial dst src n k 1 s) :
    Invariant initial dst src n (k + t) 1 (iterate byte t s) := by
  have advance : ∀ t j, j + 1 ≤ n → Invariant initial dst src n j 1 t →
      Invariant initial dst src n (j + 1) 1 (byte t) := by
    intro t j hj ht
    exact invariant_advance initial t (byte t) dst src n j 1 hn (by decide)
      hj hdst hsrc horder ht (byte_data t).1 (byte_data t).2.1
      (byte_data t).2.2.1 (byte_data t).2.2.2
  simpa only [Nat.one_mul] using invariant_iterate initial dst src n 1 byte
    advance s k t (by simpa only [Nat.one_mul] using hbound) h

/-- The descending loop produces the same original-snapshot image as the
ascending loop, also when either mathematical end address equals `2^64`. -/
theorem result_memory (s : ArmState)
    (hdst : (r (.GPR 0) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64)
    (hsrc : (r (.GPR 1) s).toNat + (r (.GPR 2) s).toNat ≤ 2 ^ 64)
    (horder : (r (.GPR 1) s).toNat ≤ (r (.GPR 0) s).toNat) :
    ∀ a, (result s).mem a = image s.mem (r (.GPR 0) s) (r (.GPR 1) s)
      (r (.GPR 2) s).toNat a := by
  let n := (r (.GPR 2) s).toNat
  let dst := r (.GPR 0) s
  let src := r (.GPR 1) s
  let t := iterate bulk (n / 16) (prefix_state s)
  have hn : n < 2 ^ 64 := by dsimp [n]; bv_omega
  have htotal : 16 * (n / 16) + n % 16 = n := by omega
  obtain ⟨hm, h1, h2, h3⟩ := prefix_state_data s
  have hstart : Invariant s dst src n 0 (if 16 ≤ n then 16 else 0)
      (prefix_state s) := by
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · simpa [src, n, apply_ite] using h1
    · simpa [n] using h2
    · simpa [dst, n, apply_ite] using h3
    · intro a
      simp only [hm, backwardImage, Nat.sub_zero]
      rw [if_neg (by omega)]
  have hbulk : Invariant s dst src n (16 * (n / 16))
      (if 16 ≤ n then 16 else 0) t := by
    by_cases hbig : 16 ≤ n
    · have hstart16 : Invariant s dst src n 0 16 (prefix_state s) := by
        simpa only [if_pos hbig] using hstart
      have h := invariant_bulk s (prefix_state s) dst src n 0 (n / 16) hn
        (by omega) hdst hsrc horder hstart16
      simpa only [if_pos hbig, Nat.zero_add] using h
    · have hq : n / 16 = 0 := by omega
      simpa only [t, hq, Nat.mul_zero, iterate] using hstart
  obtain ⟨htm, ht2, htp⟩ := tail_state_data (decide (16 ≤ n)) t
  have hmemory : ∀ a,
      (iterate byte (n % 16) (tail_state (decide (16 ≤ n)) t)).mem a =
        backwardImage s.mem dst src n n a := by
    by_cases hz : n % 16 = 0
    · have hk : 16 * (n / 16) = n := by omega
      intro a
      simpa only [hz, iterate, htm, hk] using hbulk.memory a
    · have hc : r (.GPR 2) t ≠ 0#64 := by
        rw [hbulk.count]
        have hr : n - 16 * (n / 16) = n % 16 := by omega
        rw [hr]
        have hrem : n % 16 < 16 := Nat.mod_lt _ (by decide)
        bv_omega
      obtain ⟨ht1, ht3⟩ := htp hc
      have htest : Invariant s dst src n (16 * (n / 16)) 1
          (tail_state (decide (16 ≤ n)) t) := by
        refine ⟨hbulk.bound, ?_, ?_, ?_, ?_⟩
        · rw [ht1, hbulk.source]
          by_cases hbig : 16 ≤ n <;> simp [hbig, sub16_add15]
        · rw [ht2, hbulk.count]
        · rw [ht3, hbulk.target]
          by_cases hbig : 16 ≤ n <;> simp [hbig, sub16_add15]
        · intro a
          rw [htm]
          exact hbulk.memory a
      have htail := invariant_byte s (tail_state (decide (16 ≤ n)) t)
        dst src n (16 * (n / 16)) (n % 16) hn (by omega) hdst hsrc horder htest
      intro a
      simpa only [htotal] using htail.memory a
  intro a
  simpa only [result, instruction, ArmState.mem_w_eq_mem,
    backwardImage, image, SszArm.Memcpy.image, Nat.sub_self, Nat.add_zero] using hmemory a

end Backward
end SszArm.Memmove

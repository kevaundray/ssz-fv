import SszLimbOrder

set_option autoImplicit false

namespace SszNative.Limbs

/-- The significant-count guard bounds the whole natural, not just its low words. -/
theorem width_two_bound (words : List (BitVec 64)) (h : sigWords words ≤ 2) :
    value words < 2 ^ 128 := by
  have hv := value_lt (trim words)
  rw [trim_value] at hv
  have hp : 2 ^ (64 * (trim words).length) ≤ 2 ^ 128 := by
    apply Nat.pow_le_pow_right (by decide)
    rw [trim_length]
    omega
  exact Nat.lt_of_lt_of_le hv hp

/-- Three significant limbs cannot equal a machine-sized input length. -/
theorem width_many_ne (words : List (BitVec 64)) (length : BitVec 64)
    (h : 2 < sigWords words) : value words ≠ length.toNat := by
  have hn : trim words ≠ [] := by
    intro he
    have := trim_length words
    rw [he] at this
    simp only [List.length_nil] at this
    omega
  have hv := canonical_ge_pow _ (trim_canonical words) hn
  have hp : 2 ^ 128 ≤ 2 ^ (64 * ((trim words).length - 1)) := by
    apply Nat.pow_le_pow_right (by decide)
    rw [trim_length]
    omega
  rw [trim_value] at hv
  have hl := length.isLt
  have := Nat.le_trans hp hv
  omega

/-- Stored low words reconstruct a width passing the significant-count guard,
including noncanonical Large slices and arbitrarily many redundant high zeros. -/
theorem width_two_value (words : List (BitVec 64)) (h : sigWords words ≤ 2) :
    value words = (words[0]?.getD 0).toNat + 2 ^ 64 * (words[1]?.getD 0).toNat := by
  have hb := width_two_bound words h
  cases words with
  | nil => simp [value]
  | cons lo rest =>
    cases rest with
    | nil => simp [value]
    | cons hi rest =>
      simp only [value] at hb ⊢
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      omega

/-- The native XOR/OR test is equality of mathematical naturals. -/
theorem width_pair_eq (words : List (BitVec 64)) (length : BitVec 64)
    (h : sigWords words ≤ 2) :
    (((words[0]?.getD 0) ^^^ length) ||| words[1]?.getD 0) = 0 ↔
      value words = length.toNat := by
  change (((words[0]?.getD 0) ^^^ length) ||| words[1]?.getD 0) = 0#64 ↔
    value words = length.toNat
  rw [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, width_two_value words h]
  simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat]
  have hl := length.isLt
  omega

theorem width_pair_words (words : List (BitVec 64)) (length : BitVec 64)
    (h : sigWords words ≤ 2) :
    (words[0]?.getD 0 = length ∧ words[1]?.getD 0 = 0) ↔
      value words = length.toNat := by
  change (words[0]?.getD 0 = length ∧ words[1]?.getD 0 = 0#64) ↔
    value words = length.toNat
  rw [← BitVec.xor_eq_zero_iff, ← BitVec.or_eq_zero_iff]
  exact width_pair_eq words length h

end SszNative.Limbs

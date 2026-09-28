import SszArm.MeasureScalarListWord

namespace SszArm.Measure.Scalar.Bytes

open SszNative SszNative.Limbs

theorem large_zero_value (pointer : BitVec 64) (words : List (BitVec 64))
    (zero : sigWords words = 0) : (NatOperand.large pointer words).value = 0 := by
  have upper := ((NatOperand.large pointer words).wordCount_le_iff_value_lt 0).mp
    (show (NatOperand.large pointer words).wordCount ≤ 0 by change sigWords words ≤ 0; omega)
  simp only [Nat.mul_zero, Nat.pow_zero] at upper
  omega

theorem large_one_value (pointer : BitVec 64) (words : List (BitVec 64))
    (fits : sigWords words ≤ 1) :
    (NatOperand.large pointer words).value = (words[0]?.getD 0#64).toNat := by
  have upper := ((NatOperand.large pointer words).wordCount_le_iff_value_lt 1).mp fits
  cases words with
  | nil => simp [NatOperand.value, NatOperand.words, value]
  | cons first rest =>
    simp only [NatOperand.value, NatOperand.words, value, Nat.mul_one] at upper ⊢
    simp only [List.getElem?_cons_zero, Option.getD_some]
    omega

theorem large_many_value (pointer : BitVec 64) (words : List (BitVec 64))
    (wide : 2 ≤ sigWords words) : 2^64 ≤ (NatOperand.large pointer words).value := by
  have width := (NatOperand.large pointer words).wordCount_le_iff_value_lt 1
  have notNarrow : ¬(NatOperand.large pointer words).wordCount ≤ 1 := by
    change ¬sigWords words ≤ 1
    omega
  have notSmall := mt width.mpr notNarrow
  simp only [Nat.mul_one] at notSmall
  omega

theorem width_selection (pointer : BitVec 64) (words : List (BitVec 64)) (size : Nat)
    (physical : size < 2^64)
    (different : sigWords words ≠ if size = 0 then 0 else 1) :
    (¬sigWords words < (if size = 0 then 0 else 1)) ↔
      size ≤ (NatOperand.large pointer words).value := by
  by_cases empty : size = 0
  · simp [empty]
  · simp only [empty, ↓reduceIte] at different ⊢
    by_cases zero : sigWords words = 0
    · rw [large_zero_value pointer words zero, zero]
      simp; omega
    · have wide : 2 ≤ sigWords words := by omega
      have lower := large_many_value pointer words wide
      constructor <;> intro assumption <;> omega

end SszArm.Measure.Scalar.Bytes

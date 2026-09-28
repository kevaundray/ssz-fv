import SszArm.MeasureUintCompare

namespace SszArm.Measure.Uint

theorem pairValue_join (low high : BitVec 64) :
    pairValue low high = Udivti3.join low high := by
  simp [pairValue, Udivti3.join, Udivti3.radix, Nat.add_comm]

theorem count_shift_pair (count : BitVec 64) :
    pairValue (count <<< 6) (count >>> 58) = 64 * count.toNat := by
  have bound := count.isLt
  simp only [pairValue, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

theorem count_sub57 (count : BitVec 64) (positive : 0 < count.toNat) :
    pairValue (AddWithCarry (count <<< 6) (~~~57#64) 1#1).1
      (AddWithCarry (count >>> 58) (-1#64)
        (AddWithCarry (count <<< 6) (~~~57#64) 1#1).2.c).1 =
      64 * count.toNat - 57 := by
  have shifted := count_shift_pair count
  have lower : Udivti3.join 57#64 0#64 ≤
      Udivti3.join (count <<< 6) (count >>> 58) := by
    rw [← pairValue_join, ← pairValue_join, shifted]
    simp only [pairValue, BitVec.toNat_ofNat]
    omega
  have subtracted := Udivti3.wide_subtract (count <<< 6) (count >>> 58) 57#64 0#64 lower
  rw [← pairValue_join, ← pairValue_join, shifted] at subtracted
  simpa [Udivti3.join, Udivti3.radix] using subtracted

theorem count_add_word (low high limbWord : BitVec 64)
    (bound : pairValue low high + limbWord.toNat < 2^128) :
    pairValue (AddWithCarry low limbWord 0#1).1
      (if (AddWithCarry low limbWord 0#1).2.c = 1#1 then high + 1#64 else high) =
      pairValue low high + limbWord.toNat := by
  have carry := Udivti3.adc_carry_nat low limbWord 0#1
  have lowBound := low.isLt
  have highBound := high.isLt
  have wordBound := limbWord.isLt
  have carryBound := (AddWithCarry low limbWord 0#1).2.c.isLt
  by_cases carried : (AddWithCarry low limbWord 0#1).2.c = 1#1
  · simp only [carried, ↓reduceIte, Udivti3.adc_value, pairValue, Udivti3.radix,
      BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
    omega
  · have zero : (AddWithCarry low limbWord 0#1).2.c = 0#1 := by bv_omega
    simp only [if_neg carried]
    simp only [zero, Udivti3.adc_value, pairValue, Udivti3.radix,
      BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
    omega

theorem count_shr3 (low high : BitVec 64) :
    pairValue ((low >>> 3) ||| (high <<< 61)) (high >>> 3) = pairValue low high / 8 := by
  have disjoint : (low >>> 3) &&& (high <<< 61) = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro index bound
    by_cases lower : index < 61
    · simp [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_shiftLeft, lower, bound]
    · have outside : low.getLsbD (3 + index) = false :=
        BitVec.getLsbD_of_ge low _ (by omega)
      simp [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_shiftLeft, outside]
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ disjoint]
  simp only [pairValue, BitVec.toNat_add_of_and_eq_zero disjoint,
    BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  have lowBound := low.isLt
  have highBound := high.isLt
  omega

end SszArm.Measure.Uint

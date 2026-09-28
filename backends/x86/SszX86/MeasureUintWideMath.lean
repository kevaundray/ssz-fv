import SszSerializeMeasure
import SszX86.Udivti3Math

namespace SszX86.Measure.Uint

abbrev pairValue (lo hi : BitVec 64) : Nat := lo.toNat + 2 ^ 64 * hi.toNat

def scaledLow (count : BitVec 64) : BitVec 64 := (count <<< 6) + 18446744073709551559#64

def scaledHigh (count : BitVec 64) : BitVec 64 :=
  (count >>> 58) + 18446744073709551615#64 +
    BitVec.ofNat 64 (decide (2 ^ 64 ≤ (count <<< 6).toNat + 18446744073709551559)).toNat

private theorem shift_radix :
    18446744073709551616 = 288230376151711744 * 64 := by decide

private theorem low_shift_value (count : BitVec 64) :
    (count <<< 6).toNat = count.toNat * 64 % 18446744073709551616 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

private theorem high_shift_value (count : BitVec 64) :
    (count >>> 58).toNat = count.toNat / 288230376151711744 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem scaled_quotient (n : Nat) :
    n * 64 / 18446744073709551616 = n / 288230376151711744 := by
  rw [shift_radix]
  exact Nat.mul_div_mul_right (m := 64) n 288230376151711744 (by decide)

private theorem scaled_nat_pair (n : Nat) :
    n * 64 % 18446744073709551616 +
      18446744073709551616 * (n / 288230376151711744) = n * 64 := by
  rw [← scaled_quotient n]
  exact Nat.mod_add_div (n * 64) 18446744073709551616

/-- The two shifts split multiplication by64 at the physical word boundary. -/
private theorem shifted_pair_value (count : BitVec 64) :
    (count <<< 6).toNat + 18446744073709551616 * (count >>> 58).toNat =
      64 * count.toNat := by
  rw [low_shift_value, high_shift_value, scaled_nat_pair]
  exact Nat.mul_comm count.toNat 64

private theorem subtract57_carry (lo : BitVec 64) (enough : 57 ≤ lo.toNat) :
    (lo + 18446744073709551559#64).toNat = lo.toNat - 57 := by
  rw [show 18446744073709551559#64 = -(57#64) by decide, BitVec.add_neg_eq_sub]
  apply BitVec.toNat_sub_of_le
  change 57 ≤ lo.toNat
  exact enough

private theorem subtract57_no_carry (lo : BitVec 64) (short : lo.toNat < 57) :
    (lo + 18446744073709551559#64).toNat = lo.toNat + 18446744073709551559 := by
  apply BitVec.toNat_add_of_lt
  change lo.toNat + 18446744073709551559 < 18446744073709551616
  omega

private theorem subtract_one_value (hi : BitVec 64) (positive : 0 < hi.toNat) :
    (hi + 18446744073709551615#64).toNat = hi.toNat - 1 := by
  rw [show 18446744073709551615#64 = -(1#64) by decide, BitVec.add_neg_eq_sub]
  apply BitVec.toNat_sub_of_le
  change 1 ≤ hi.toNat
  exact positive

private theorem scaled_high_carry (count : BitVec 64)
    (carry : 18446744073709551616 ≤ (count <<< 6).toNat + 18446744073709551559) :
    scaledHigh count = count >>> 58 := by
  have carryBit : BitVec.ofNat 64
      (decide (2 ^ 64 ≤ (count <<< 6).toNat + 18446744073709551559)).toNat = 1#64 := by
    simp only [show 2 ^ 64 = 18446744073709551616 by rfl, carry, decide_true, Bool.toNat_true]
  unfold scaledHigh
  rw [carryBit, BitVec.add_assoc]
  rw [show 18446744073709551615#64 + 1#64 = 0#64 by decide, BitVec.add_zero]

private theorem scaled_high_no_carry (count : BitVec 64)
    (carry : ¬ 18446744073709551616 ≤ (count <<< 6).toNat + 18446744073709551559)
    (positive : 0 < (count >>> 58).toNat) :
    (scaledHigh count).toNat = (count >>> 58).toNat - 1 := by
  have carryBit : BitVec.ofNat 64
      (decide (2 ^ 64 ≤ (count <<< 6).toNat + 18446744073709551559)).toNat = 0#64 := by
    simp only [show 2 ^ 64 = 18446744073709551616 by rfl, carry, decide_false, Bool.toNat_false]
  unfold scaledHigh
  rw [carryBit, BitVec.add_zero]
  exact subtract_one_value (count >>> 58) positive

/-- SHL/SHR and the two carry-producing additions compute 64*(count-1)+7
without narrowing the intermediate bit count to 64 bits. -/
theorem scaled_value (count : BitVec 64) (positive : 0 < count.toNat) :
    pairValue (scaledLow count) (scaledHigh count) = 64 * (count.toNat - 1) + 7 := by
  have shifted := shifted_pair_value count
  by_cases carry : 18446744073709551616 ≤
      (count <<< 6).toNat + 18446744073709551559
  · have low := subtract57_carry (count <<< 6) (by omega)
    have high := scaled_high_carry count carry
    unfold pairValue scaledLow
    rw [low, high]
    omega
  · have low := subtract57_no_carry (count <<< 6) (by omega)
    have highPositive : 0 < (count >>> 58).toNat := by omega
    have high := scaled_high_no_carry count carry highPositive
    unfold pairValue scaledLow
    rw [low, high]
    omega

def sumLow (lo increment : BitVec 64) : BitVec 64 := lo + increment

def sumHigh (lo hi increment : BitVec 64) : BitVec 64 :=
  hi + BitVec.ofNat 64 (decide (2 ^ 64 ≤ lo.toNat + increment.toNat)).toNat

/-- Carry from the low limb participates in the high limb before division. -/
theorem sum_value (lo hi increment : BitVec 64)
    (bounded : pairValue lo hi + increment.toNat < 2 ^ 128) :
    pairValue (sumLow lo increment) (sumHigh lo hi increment) =
      pairValue lo hi + increment.toNat := by
  have loBound := lo.isLt
  have hiBound := hi.isLt
  have incrementBound := increment.isLt
  unfold pairValue sumLow sumHigh at *
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  by_cases carry : 2 ^ 64 ≤ lo.toNat + increment.toNat <;> simp [carry] <;> omega

def dividedLow (lo hi : BitVec 64) : BitVec 64 := ((hi ++ lo) >>> 3).setWidth 64

def dividedHigh (hi : BitVec 64) : BitVec 64 := hi >>> 3

/-- SHRD/SHR are division of the complete 128-bit pair by eight. -/
theorem divided_value (lo hi : BitVec 64) :
    pairValue (dividedLow lo hi) (dividedHigh hi) = pairValue lo hi / 8 := by
  have loBound := lo.isLt
  have hiBound := hi.isLt
  unfold pairValue dividedLow dividedHigh
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt loBound, Nat.shiftLeft_eq]
  omega

/-- INC32 is safe because the lowered BSR result is in0..63. -/
theorem bit_count_increment (highest : BitVec 64) (bound : highest.toNat < 64) :
    ((highest.setWidth 32 + 1#32).setWidth 64).toNat = highest.toNat + 1 := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Byte rounding accepts the full bit count before the original width comparison. -/
theorem rounded_pair (lo hi highest : BitVec 64)
    (highestBound : highest.toNat < 64)
    (bounded : pairValue lo hi + highest.toNat + 1 < 2 ^ 128) :
    pairValue
      (dividedLow (sumLow lo ((highest.setWidth 32 + 1#32).setWidth 64))
        (sumHigh lo hi ((highest.setWidth 32 + 1#32).setWidth 64)))
      (dividedHigh (sumHigh lo hi ((highest.setWidth 32 + 1#32).setWidth 64))) =
        (pairValue lo hi + highest.toNat + 1) / 8 := by
  rw [divided_value, sum_value]
  · rw [bit_count_increment highest highestBound]
    congr 1
  · rw [bit_count_increment highest highestBound]
    omega

end SszX86.Measure.Uint

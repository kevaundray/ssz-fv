import SszX86.BitVectorCore

namespace SszX86.BitVector

abbrev constructLow (count : BitVec 128) : BitVec 64 := count.setWidth 64
abbrev constructHigh (count : BitVec 128) : BitVec 64 :=
  (count >>> (64 : Nat)).setWidth 64

/-- The exact double-left-shift expression evaluated by native SHLD $61. -/
def constructQuotient (count : BitVec 128) : BitVec 64 :=
  (((constructHigh count ++ constructLow count) <<< (61 : Nat)).extractLsb' 64 64)

/-- TEST AL,7 followed by SETNE into an otherwise zero RDI. -/
def constructBump (count : BitVec 128) : BitVec 64 :=
  BitVec.ofNat 64 (!(((constructLow count).extractLsb' 0 8 &&& 7#8) == 0#8)).toNat

theorem construct_halves (count : BitVec 128) :
    constructHigh count ++ constructLow count = count := by
  rw [constructHigh, BitVec.setWidth_ushiftRight_eq_extractLsb,
    constructLow, BitVec.setWidth_eq_extractLsb' (by decide)]
  exact BitVec.extractLsb'_append_extractLsb'

theorem construct_quotient_nat (count : BitVec 128) (bound : count.toNat < 2^67) :
    (constructQuotient count).toNat = count.toNat / 8 := by
  rw [constructQuotient, construct_halves]
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

theorem construct_high_shift (count : BitVec 128) (bound : count.toNat < 2^67) :
    constructHigh count >>> (3 : Nat) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [constructHigh, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  omega

theorem construct_tail_nat (count : BitVec 128) :
    ((constructLow count).extractLsb' 0 8 &&& 7#8).toNat = count.toNat % 8 := by
  simp only [constructLow, BitVec.toNat_and, BitVec.extractLsb'_toNat,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  change (count.toNat % 2^64 % 2^8 &&& (2^3 - 1)) = count.toNat % 8
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem construct_bump_nat (count : BitVec 128) :
    (constructBump count).toNat = if count.toNat % 8 = 0 then 0 else 1 := by
  have zero : ((constructLow count).extractLsb' 0 8 &&& 7#8) = 0#8 ↔
      count.toNat % 8 = 0 := by
    constructor
    · intro h
      simpa only [h, BitVec.toNat_ofNat] using (construct_tail_nat count).symm
    · intro h
      apply BitVec.eq_of_toNat_eq
      simpa only [h, BitVec.toNat_ofNat] using construct_tail_nat count
  have normalized : (count.setWidth 8 &&& 7#8) = 0#8 ↔ count.toNat % 8 = 0 := by
    simpa [constructLow] using zero
  by_cases tail : count.toNat % 8 = 0
  · simp [constructBump, normalized.mpr tail, tail]
  · have nonzero := mt normalized.mp tail
    simp [constructBump, beq_eq_false_iff_ne.mpr nonzero, tail]

/-- Scope's physical 64-bit length excludes the sole possible rounding carry.
The native ADD result is the original length, and ADC receives carry=false. -/
theorem construct_rounding (count : BitVec 128) (size : BitVec 64)
    (bound : count.toNat < 2^67) (scope : size.toNat = (count.toNat + 7) / 8) :
    constructQuotient count + constructBump count = size ∧
      (SszX86.Udivti3.addFlags (constructQuotient count) (constructBump count)).cf = false := by
  have quotient := construct_quotient_nat count bound
  have bump := construct_bump_nat count
  have lengthBound := size.isLt
  have sum : (constructQuotient count).toNat + (constructBump count).toNat = size.toNat := by
    rw [quotient, bump]
    split <;> omega
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, sum, Nat.mod_eq_of_lt lengthBound]
  · rw [SszX86.Udivti3.addFlags_cf]
    simp only [SszX86.Udivti3.radix, sum, decide_eq_false_iff_not]
    omega

end SszX86.BitVector

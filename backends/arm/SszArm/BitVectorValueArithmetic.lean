import SszArm.BitVectorValueLoadExec
import SszArm.UintShifts
import SszArm.Udivti3Arithmetic

namespace SszArm.BitVector.ValueTail

abbrev countLow (count : BitVec 128) : BitVec 64 := count.setWidth 64
abbrev countHigh (count : BitVec 128) : BitVec 64 := (count >>> (64 : Nat)).setWidth 64

def quotientWord (low high : BitVec 64) : BitVec 64 :=
  shift3 low ||| (high <<< (61 : Nat))

def roundWord (low : BitVec 64) : BitVec 64 :=
  if low &&& 7#64 = 0#64 then 0#64 else 1#64

theorem shift3_eq (word : BitVec 64) : shift3 word = word >>> (3 : Nat) :=
  UintCodec.uint_lsr3_mask word

theorem mask7_nat (word : BitVec 64) : (word &&& 7#64).toNat = word.toNat % 8 := by
  change word.toNat &&& (2^3 - 1) = word.toNat % 2^3
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem count_words (count : BitVec 128) :
    count.toNat = 18446744073709551616 * (countHigh count).toNat +
      (countLow count).toNat := by
  have bound := count.isLt
  simp only [countHigh, countLow, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  omega

theorem roundWord_nat (word : BitVec 64) :
    (roundWord word).toNat = if word.toNat % 8 = 0 then 0 else 1 := by
  have zero : word &&& 7#64 = 0#64 ↔ word.toNat % 8 = 0 := by
    rw [← mask7_nat]
    exact ⟨congrArg BitVec.toNat, fun equal => BitVec.eq_of_toNat_eq equal⟩
  simp only [roundWord, zero]
  split <;> rfl

/-- The register pair is not narrowed to a single u64: a successful scope permits
up to 67 significant input bits. Only the rounded byte count is a u64. -/
theorem quotientWord_nat (low high : BitVec 64) (highBound : high.toNat < 8) :
    (quotientWord low high).toNat =
      2305843009213693952 * high.toNat + low.toNat / 8 := by
  have lowBound := low.isLt
  have shiftedBound : high.toNat <<< 61 < 2^64 := by
    rw [Nat.shiftLeft_eq]
    omega
  have quotientBound : low.toNat / 8 < 2^61 := by omega
  simp only [quotientWord, shift3_eq, BitVec.toNat_or, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_shiftLeft,
    Nat.mod_eq_of_lt shiftedBound]
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt quotientBound high.toNat,
    Nat.shiftLeft_eq]
  omega

/-- Numeric scope implies both zero high quotient and absence of ADDS carry.
Thus neither the carry increment nor the final bad-representation branch is
assumed away. They are excluded by the observed usize equality. -/
theorem scope_registers (count : BitVec 128) (actual : BitVec 64)
    (scope : actual.toNat = (count.toNat + 7) / 8) :
    shift3 (countHigh count) = 0#64 ∧
    quotientWord (countLow count) (countHigh count) + roundWord (countLow count) = actual ∧
    (AddWithCarry (quotientWord (countLow count) (countHigh count))
      (roundWord (countLow count)) 0#1).2.c = 0#1 := by
  have actualBound := actual.isLt
  have words := count_words count
  have lowBound := (countLow count).isLt
  have highBound : (countHigh count).toNat < 8 := by omega
  have quotient := quotientWord_nat (countLow count) (countHigh count) highBound
  have rounded := roundWord_nat (countLow count)
  have modulo : (countLow count).toNat % 8 = count.toNat % 8 := by omega
  have total : (quotientWord (countLow count) (countHigh count)).toNat +
      (roundWord (countLow count)).toNat = actual.toNat := by
    rw [quotient, rounded, modulo]
    split <;> omega
  refine ⟨?_, ?_, ?_⟩
  · rw [shift3_eq]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
    omega
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, total, Nat.mod_eq_of_lt actualBound]
  · have carry := Udivti3.adc_carry
      (quotientWord (countLow count) (countHigh count)) (roundWord (countLow count)) 0#1
    have notOne : (AddWithCarry (quotientWord (countLow count) (countHigh count))
        (roundWord (countLow count)) 0#1).2.c ≠ 1#1 := by
      intro equal
      have overflow := carry.mp equal
      simp only [Udivti3.radix, BitVec.toNat_ofNat, Nat.add_zero] at overflow
      omega
    bv_omega

end SszArm.BitVector.ValueTail

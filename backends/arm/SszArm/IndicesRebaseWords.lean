import SszArm.IndicesRebaseArithmetic
import SszArm.IndicesRebaseEntry

set_option autoImplicit false

namespace SszArm.Indices.Rebase.Words

open SszArm.Udivti3 (join radix)

/-- Actual low ADDS and the carry-selected high ADD at offsets 12--28. -/
def incrementLow (low : BitVec 64) : BitVec 64 := low + 1#64

def incrementHigh (low high : BitVec 64) : BitVec 64 :=
  if (AddWithCarry low 1#64 0#1).2.c = 1#1 then high + 1#64 else high

/-- The AND/CMN guard rejects exactly u128::MAX, not either maximum half. -/
theorem increment_guard (low high : BitVec 64) :
    (AddWithCarry (low &&& high) 1#64 0#1).2.z = 1#1 ↔
      2^128 ≤ join low high + 1 := by
  have flag : (AddWithCarry (low &&& high) 1#64 0#1).2.z = 1#1 ↔
      low &&& high = BitVec.allOnes 64 := by
    change (if (AddWithCarry (low &&& high) 1#64 0#1).1 = 0#64 then 1#1 else 0#1) = 1#1 ↔ _
    rw [Udivti3.adc_value]
    have maskBound := (low &&& high).isLt
    have maxEq : low &&& high = BitVec.allOnes 64 ↔
        (low &&& high).toNat = 2^64 - 1 := by
      constructor
      · intro h; simp [h]
      · intro h; apply BitVec.eq_of_toNat_eq; simpa using h
    rw [maxEq]
    have zeroEq : low &&& high + 1#64 + (0#1).setWidth 64 = 0#64 ↔
        ((low &&& high).toNat + 1) % 2^64 = 0 := by
      constructor
      · intro h
        have value := congrArg BitVec.toNat h
        simpa only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
          Nat.add_zero, Nat.mod_mod] using value
      · intro h
        apply BitVec.eq_of_toNat_eq
        simpa only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
          Nat.add_zero, Nat.mod_mod] using h
    rw [zeroEq]
    split <;> simp_all <;> omega
  rw [flag, BitVec.and_eq_allOnes_iff]
  have lowEq : low = BitVec.allOnes 64 ↔ low.toNat = 2^64 - 1 := by
    constructor
    · intro h; simp [h]
    · intro h; apply BitVec.eq_of_toNat_eq; simpa using h
  have highEq : high = BitVec.allOnes 64 ↔ high.toNat = 2^64 - 1 := by
    constructor
    · intro h; simp [h]
    · intro h; apply BitVec.eq_of_toNat_eq; simpa using h
  rw [lowEq, highEq]
  have lowBound := low.isLt
  have highBound := high.isLt
  dsimp only [join, radix]
  omega

/-- Successful checked addition retains its full high word. -/
theorem increment_value (low high : BitVec 64)
    (fits : join low high + 1 < 2^128) :
    join (incrementLow low) (incrementHigh low high) = join low high + 1 := by
  have lowBound := low.isLt
  have highBound := high.isLt
  have carry := Udivti3.adc_carry low 1#64 0#1
  simp only [BitVec.toNat_ofNat, Nat.add_zero] at carry
  unfold incrementHigh
  split
  · rename_i carried
    have overflow := carry.mp carried
    simp only [incrementLow, join, BitVec.toNat_add, BitVec.toNat_ofNat]
    dsimp only [join, radix] at fits ⊢
    omega
  · rename_i notCarried
    have bounded : ¬ radix ≤ low.toNat + 1 := fun h => notCarried (carry.mpr h)
    simp only [incrementLow, join, BitVec.toNat_add, BitVec.toNat_ofNat]
    dsimp only [join, radix] at fits bounded ⊢
    omega

/-- LSR/ORR keeps both halves of the u128 quotient. -/
def quotientLow (low high : BitVec 64) : BitVec 64 :=
  (low >>> (6 : Nat)) ||| (high <<< (58 : Nat))

def quotientHigh (high : BitVec 64) : BitVec 64 := high >>> (6 : Nat)

theorem quotientLow_nat (low high : BitVec 64) :
    (quotientLow low high).toNat = 2^58 * (high.toNat % 64) + low.toNat / 64 := by
  have lowBound := low.isLt
  have quotientBound : low.toNat / 64 < 2^58 := by omega
  have shifted : (high <<< (58 : Nat)).toNat = (high.toNat % 64) <<< 58 := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    omega
  simp only [quotientLow, BitVec.toNat_or, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, shifted]
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt quotientBound (high.toNat % 64),
    Nat.shiftLeft_eq]
  omega

theorem quotient_value (low high : BitVec 64) :
    join (quotientLow low high) (quotientHigh high) = join low high / 64 := by
  have quotient := quotientLow_nat low high
  have lowBound := low.isLt
  simp only [join, quotientHigh, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    quotient, radix]
  omega

/-- Offset 32 tests the increment's remainder before any count truncation. -/
theorem remainder_zero (low high : BitVec 64) :
    low &&& 63#64 = 0#64 ↔ join low high % 64 = 0 := by
  have masked : (low &&& 63#64).toNat = low.toNat % 64 := by
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    exact Nat.and_two_pow_sub_one_eq_mod low.toNat 6
  have zero : low &&& 63#64 = 0#64 ↔ (low &&& 63#64).toNat = 0 := by
    constructor
    · intro h; simp [h]
    · intro h; exact BitVec.eq_of_toNat_eq h
  rw [zero, masked]
  dsimp only [join, radix]
  omega

def roundWord (low : BitVec 64) : BitVec 64 :=
  if low &&& 63#64 = 0#64 then 0#64 else 1#64

def countLow (low high : BitVec 64) : BitVec 64 :=
  quotientLow low high + roundWord low

def countHigh (low high : BitVec 64) : BitVec 64 :=
  if (AddWithCarry (quotientLow low high) (roundWord low) 0#1).2.c = 1#1
  then quotientHigh high + 1#64 else quotientHigh high

theorem roundWord_nat (low high : BitVec 64) :
    (roundWord low).toNat = if join low high % 64 = 0 then 0 else 1 := by
  simp only [roundWord, remainder_zero low high]
  split <;> rfl

/-- The count addition's carry is retained in X11; CBZ X11 is a checked usize
conversion, not a low-half cast. -/
theorem count_value (low high : BitVec 64) :
    join (countLow low high) (countHigh low high) =
      join low high / 64 + (if join low high % 64 = 0 then 0 else 1) := by
  have quotient := quotient_value low high
  have highBound := high.isLt
  have lowBound := (quotientLow low high).isLt
  have round := roundWord_nat low high
  have roundBound : (roundWord low).toNat ≤ 1 := by rw [round]; split <;> omega
  have carry := Udivti3.adc_carry (quotientLow low high) (roundWord low) 0#1
  simp only [BitVec.toNat_ofNat, Nat.add_zero] at carry
  have highQuotient : (quotientHigh high).toNat = high.toNat / 64 := by
    simp [quotientHigh, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  unfold countHigh
  split
  · rename_i carried
    have overflow := carry.mp carried
    simp only [countLow, join, BitVec.toNat_add, BitVec.toNat_ofNat, highQuotient]
    dsimp only [join, radix] at quotient overflow ⊢
    rw [highQuotient] at quotient
    omega
  · rename_i notCarried
    have bounded : ¬ radix ≤ (quotientLow low high).toNat + (roundWord low).toNat :=
      fun h => notCarried (carry.mpr h)
    simp only [countLow, join, BitVec.toNat_add, highQuotient]
    dsimp only [join, radix] at quotient bounded ⊢
    rw [highQuotient] at quotient
    omega

theorem count_checked (low high : BitVec 64) :
    countHigh low high = 0#64 ↔
      join low high / 64 + (if join low high % 64 = 0 then 0 else 1) < 2^64 := by
  have value := count_value low high
  have lowBound := (countLow low high).isLt
  have zero : countHigh low high = 0#64 ↔ (countHigh low high).toNat = 0 := by
    constructor
    · intro h; simp [h]
    · intro h; exact BitVec.eq_of_toNat_eq h
  rw [zero]
  dsimp only [join, radix] at value
  omega

/-- Combined exact boundary at the original count-dispatch CBZ. -/
theorem checked_increment_count (low high : BitVec 64)
    (fits : join low high + 1 < 2^128) :
    countHigh (incrementLow low) (incrementHigh low high) = 0#64 ↔
      join low high < 64 * (2^64 - 1) := by
  rw [count_checked, increment_value low high fits, Rebase.increment_count,
    Rebase.count_fits_iff]

end SszArm.Indices.Rebase.Words

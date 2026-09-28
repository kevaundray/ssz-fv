import SszArm.NatMulProduct
import SszArm.Udivti3Arithmetic

namespace SszArm.NatMulProduct

local notation "B" => (2 ^ 64 : Nat)

/-- The zero-extended C flag produced by the actual low-word ADDS. -/
def carryWord (a b : BitVec 64) : BitVec 64 :=
  (AddWithCarry a b 0#1).2.c.setWidth 64

theorem carryWord_toNat (a b : BitVec 64) :
    (carryWord a b).toNat = (a.toNat + b.toNat) / B := by
  rw [carryWord, BitVec.toNat_setWidth_of_le (by decide : 1 ≤ 64)]
  simpa only [Udivti3.radix, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero] using
    Udivti3.adc_carry_nat a b 0#1

theorem carryWord_eq_cset (a b : BitVec 64) :
    carryWord a b =
      if (AddWithCarry a b 0#1).2.c = 1#1 then 1#64 else 0#64 := by
  have bound := (AddWithCarry a b 0#1).2.c.isLt
  by_cases h : (AddWithCarry a b 0#1).2.c = 1#1
  · simp [carryWord, h]
  · have hz : (AddWithCarry a b 0#1).2.c = 0#1 := by
      apply BitVec.eq_of_toNat_eq
      have hn : (AddWithCarry a b 0#1).2.c.toNat ≠ 1 := by
        intro hn
        apply h
        apply BitVec.eq_of_toNat_eq
        simpa using hn
      simp only [BitVec.toNat_ofNat]
      omega
    simp [carryWord, h, hz]

theorem add_value (a b : BitVec 64) :
    (a + b).toNat + B * (carryWord a b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, carryWord_toNat]
  exact Nat.mod_add_div _ B

/-- The two carry increments of the high limb never overflow. This follows
from the checked shared product bound, not a machine-state precondition. -/
theorem step_high_bound (a b old carry : BitVec 64) :
    (high a b).toNat + (carryWord (a * b) old).toNat +
      (carryWord (a * b + old) carry).toNat < B := by
  have product := product_value a b
  have first := add_value (a * b) old
  have second := add_value (a * b + old) carry
  have bound := SszNative.LimbMul.product_lt a b old carry.toNat carry.isLt
  omega

/-- The actual low ADDS/high carry increment chain implements the one checked
LimbMul step, for every pair of inputs and every 64-bit old limb and carry. -/
theorem step_eq (a b old carry : BitVec 64) :
    SszNative.LimbMul.step a b old carry.toNat =
      (a * b + old + carry,
        (high a b + carryWord (a * b) old +
          carryWord (a * b + old) carry).toNat) := by
  have product := product_value a b
  have first := add_value (a * b) old
  have second := add_value (a * b + old) carry
  have lowBound := (a * b + old + carry).isLt
  have highBound := step_high_bound a b old carry
  have firstBound : (high a b).toNat + (carryWord (a * b) old).toNat < B := by
    omega
  apply Prod.ext
  · apply BitVec.eq_of_toNat_eq
    simp only [SszNative.LimbMul.step, BitVec.toNat_ofNat]
    omega
  · simp only [SszNative.LimbMul.step, BitVec.toNat_add,
      Nat.mod_eq_of_lt firstBound, Nat.mod_eq_of_lt highBound]
    omega

/-- The emitted low word, independently of the high-limb implementation. -/
theorem step_low (a b old carry : BitVec 64) :
    a * b + old + carry = (SszNative.LimbMul.step a b old carry.toNat).1 := by
  rw [step_eq]

/-- Exact natural outgoing carry, including both low-word overflows. -/
theorem step_high (a b old carry : BitVec 64) :
    (high a b + carryWord (a * b) old +
      carryWord (a * b + old) carry).toNat =
        (SszNative.LimbMul.step a b old carry.toNat).2 := by
  rw [step_eq]

/-- The same checked step when the lowering adds the incoming carry before
loading and adding the old destination limb. -/
theorem step_eq_carry_first (a b old carry : BitVec 64) :
    SszNative.LimbMul.step a b old carry.toNat =
      (a * b + carry + old,
        (high a b + carryWord (a * b) carry +
          carryWord (a * b + carry) old).toNat) := by
  have h := step_eq a b carry old
  have swap : SszNative.LimbMul.step a b old carry.toNat =
      SszNative.LimbMul.step a b carry old.toNat := by
    simp only [SszNative.LimbMul.step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  exact swap.trans h

/-- An ADDS followed by ADC-to-high, repeated for the second addend. Flags
are those computed by AddWithCarry itself, rather than assumed booleans. -/
theorem step_eq_adc (a b old carry : BitVec 64) :
    let first := AddWithCarry (a * b) old 0#1
    let firstHigh := AddWithCarry (high a b) 0#64 first.2.c
    let last := AddWithCarry first.1 carry 0#1
    let lastHigh := AddWithCarry firstHigh.1 0#64 last.2.c
    SszNative.LimbMul.step a b old carry.toNat = (last.1, lastHigh.1.toNat) := by
  simpa only [NatMulArithmetic.carry_result, BitVec.setWidth_zero,
    BitVec.add_zero, carryWord] using step_eq a b old carry

theorem step_eq_adc_carry_first (a b old carry : BitVec 64) :
    let first := AddWithCarry (a * b) carry 0#1
    let firstHigh := AddWithCarry (high a b) 0#64 first.2.c
    let last := AddWithCarry first.1 old 0#1
    let lastHigh := AddWithCarry firstHigh.1 0#64 last.2.c
    SszNative.LimbMul.step a b old carry.toNat = (last.1, lastHigh.1.toNat) := by
  simpa only [NatMulArithmetic.carry_result, BitVec.setWidth_zero,
    BitVec.add_zero, carryWord] using step_eq_carry_first a b old carry

end SszArm.NatMulProduct

import SszX86.NatMulWordCore
import SszX86.Udivti3Math

namespace SszX86.NatMulWord
open SszNative

/-- The high register value produced by the actual unsigned MUL semantics. -/
def productHigh (factor limb : BitVec 64) : BitVec 64 :=
  BitVec.ofInt 64 ((factor.unsigned * limb.unsigned) >>> 64)

theorem productHigh_eq (factor limb : BitVec 64) :
    productHigh factor limb = BitVec.ofNat 64 (factor.toNat * limb.toNat / 2^64) := by
  simp only [productHigh, BitVec.unsigned, ← Int.natCast_mul,
    ← Int.natCast_shiftRight, BitVec.ofInt_natCast, Nat.shiftRight_eq_div_pow]

theorem mul_low (factor limb : BitVec 64) :
    factor * limb = (LimbMul.wideProduct factor limb 0 0).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth,
    LimbMul.wideProduct_toNat factor limb 0 0 (by decide),
    show (0 : BitVec 64).toNat = 0 by decide, Nat.add_zero]

theorem mul_high (factor limb : BitVec 64) :
    productHigh factor limb = ((LimbMul.wideProduct factor limb 0 0) >>> 64).setWidth 64 := by
  rw [productHigh_eq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, LimbMul.wideProduct_toNat factor limb 0 0 (by decide),
    show (0 : BitVec 64).toNat = 0 by decide, Nat.add_zero]

/-- Two ADD/ADC pairs preserve the full widened multiplication, including the
possible carry from each low addition. This is shared by mul and mul_word. -/
theorem add_carry_step (factor limb old : BitVec 64) (carry : Nat) (hc : carry < 2^64) :
    factor * limb + BitVec.ofNat 64 carry + old = (LimbMul.step factor limb old carry).1 ∧
    productHigh factor limb +
      BitVec.ofNat 64 (Udivti3.addFlags (factor * limb) (BitVec.ofNat 64 carry)).cf.toNat +
      BitVec.ofNat 64 (Udivti3.addFlags (factor * limb + BitVec.ofNat 64 carry) old).cf.toNat =
        BitVec.ofNat 64 (LimbMul.step factor limb old carry).2 := by
  have totalBound := LimbMul.product_lt factor limb old carry hc
  have oldBound := old.isLt
  have productBound := LimbMul.product_lt factor limb 0 0 (by decide)
  simp only [show (0 : BitVec 64).toNat = 0 by decide, Nat.add_zero] at productBound
  have carryNat : (BitVec.ofNat 64 carry).toNat = carry := Nat.mod_eq_of_lt hc
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp only [LimbMul.step, BitVec.toNat_mul, BitVec.toNat_add,
      BitVec.toNat_ofNat, Nat.mod_add_mod]
    congr 1
    omega
  · rw [productHigh_eq, Udivti3.addFlags_cf, Udivti3.addFlags_cf]
    simp only [BitVec.toNat_add, BitVec.toNat_mul, carryNat, Udivti3.radix]
    by_cases first : 2^64 ≤ factor.toNat * limb.toNat % 2^64 + carry <;>
      by_cases second : 2^64 ≤ (factor.toNat * limb.toNat % 2^64 + carry) % 2^64 + old.toNat
    all_goals
      simp only [first, second, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false]
      apply BitVec.eq_of_toNat_eq
      simp only [LimbMul.step, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega

/-- The helper's destination has no old word: it is a one-ADD/ADC recurrence. -/
theorem word_carry_step (factor limb : BitVec 64) (carry : Nat) (hc : carry < 2^64) :
    factor * limb + BitVec.ofNat 64 carry = (LimbMul.step factor limb 0 carry).1 ∧
    productHigh factor limb +
      BitVec.ofNat 64 (Udivti3.addFlags (factor * limb) (BitVec.ofNat 64 carry)).cf.toNat =
        BitVec.ofNat 64 (LimbMul.step factor limb 0 carry).2 := by
  have step := add_carry_step factor limb 0 carry hc
  have noCarry : (Udivti3.addFlags (factor * limb + BitVec.ofNat 64 carry) 0).cf = false := by
    rw [Udivti3.addFlags_cf]
    simp only [show (0 : BitVec 64).toNat = 0 by decide, Nat.add_zero, Udivti3.radix]
    exact decide_eq_false (by have := (factor * limb + BitVec.ofNat 64 carry).isLt; omega)
  rw [noCarry] at step
  simpa only [Bool.toNat_false, show BitVec.ofNat 64 0 = 0#64 by rfl,
    show (0 : BitVec 64) = 0#64 by decide, BitVec.add_zero] using step

end SszX86.NatMulWord

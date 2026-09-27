import SszArm.NatDivisionArithmetic
import SszNatOperandNormalization

namespace SszArm.NatDivision

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The runtime's return pair is the unique radix-2^64 decomposition. -/
theorem join_unique (al ah bl bh : BitVec 64)
    (eq : Udivti3.join al ah = Udivti3.join bl bh) : al = bl ∧ ah = bh := by
  have alBound := al.isLt
  have blBound := bl.isLt
  simp only [Udivti3.join, Udivti3.radix] at eq
  constructor <;> apply BitVec.eq_of_toNat_eq <;> omega

theorem join_wide (value : BitVec 128) :
    Udivti3.join (value.setWidth 64) ((value >>> 64).setWidth 64) = value.toNat := by
  have bounded := value.isLt
  have high : value.toNat / 2^64 < 2^64 := by omega
  rw [Udivti3.join_eq]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt high, Udivti3.radix]
  omega

/-- Fast-path quotient registers match the frozen source model's u128 result. -/
theorem call_wide_quotient (site : CallSite) (s : ArmState) (base : BitVec 64)
    (operand : SszNative.NatOperand) (divisor : BitVec 64)
    (count : operand.wordCount ≤ 2) (numerator : Udivti3.numerator s = operand.value)
    (denominator : Udivti3.divisor s = divisor.toNat) (positive : 0 < divisor.toNat) :
    r (.GPR 0#5) (callResult site s base) =
        (SszNative.NatDivision.wideQuotient operand divisor).setWidth 64 ∧
      r (.GPR 1#5) (callResult site s base) =
        (SszNative.NatDivision.wideQuotient operand divisor >>> 64).setWidth 64 := by
  have quotient := call_quotient site s base (by rw [denominator]; exact positive)
  rw [numerator, denominator] at quotient
  apply join_unique
  exact quotient.trans ((SszNative.NatDivision.wideQuotient_toNat operand divisor count).symm.trans
    (join_wide _).symm)

/-- Testing the returned high word is exactly the source model's Small test. -/
theorem high_zero_iff (lo hi : BitVec 64) :
    hi = 0#64 ↔ Udivti3.join lo hi < 2^64 := by
  have lowBound := lo.isLt
  have highBound := hi.isLt
  have zero : hi = 0#64 ↔ hi.toNat = 0 := by
    constructor
    · intro h; simp [h]
    · intro h; exact BitVec.eq_of_toNat_eq h
  rw [zero]
  simp only [Udivti3.join, Udivti3.radix]
  omega

theorem wide_high_zero_iff (value : BitVec 128) :
    (value >>> 64).setWidth 64 = 0#64 ↔ value.toNat < 2^64 := by
  rw [high_zero_iff (value.setWidth 64), join_wide]

/-- The MUL/SUB remainder sequence is the exact frozen wide remainder. -/
theorem wide_remainder_low (operand : SszNative.NatOperand) (divisor low high ql qh : BitVec 64)
    (count : operand.wordCount ≤ 2) (nonzero : divisor ≠ 0#64)
    (input : Udivti3.join low high = operand.value)
    (quotient : Udivti3.join ql qh = operand.value / divisor.toNat) :
    low - ql * divisor = SszNative.NatDivision.wideRemainder operand divisor := by
  have identity := remainder_low low high divisor ql qh (by rw [input]; exact quotient)
  rw [identity]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, input,
    SszNative.NatDivision.wideRemainder_toNat operand divisor count nonzero]
  have positive : 0 < divisor.toNat := by
    apply Nat.pos_of_ne_zero
    intro zero
    apply nonzero
    apply BitVec.eq_of_toNat_eq
    simpa using zero
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ positive) divisor.isLt)

end SszArm.NatDivision

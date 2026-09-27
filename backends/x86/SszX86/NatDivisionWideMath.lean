import SszX86.NatDivisionCore

namespace SszX86.NatDivision
open SszNative

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- The fast path reads exactly the first two original words, including zero
extension and any physically retained but semantically redundant high words. -/
theorem input_pair (operand : NatOperand) (count : operand.wordCount ≤ 2) :
    Udivti3.value (operand.words[0]?.getD 0) (operand.words[1]?.getD 0) = operand.value := by
  have bound := SszNative.NatDivision.value_lt_128 operand count
  change Limbs.value operand.words < 2^128 at bound
  change Udivti3.value (operand.words[0]?.getD 0) (operand.words[1]?.getD 0) =
    Limbs.value operand.words
  generalize operand.words = words at *
  cases words with
  | nil => rfl
  | cons lo rest =>
    cases rest with
    | nil => simp [Udivti3.value, Limbs.value]
    | cons hi rest =>
      have highZero : Limbs.value rest = 0 := by
        change Limbs.value (lo :: hi :: rest) < 2^128 at bound
        simp only [Limbs.value] at bound
        omega
      change hi.toNat * 2^64 + lo.toNat = Limbs.value (lo :: hi :: rest)
      simp only [Limbs.value, highZero, Nat.mul_zero, Nat.add_zero]
      omega

/-- Splitting the actual RDX:RAX quotient recovers precisely the two fields
used by the shared from_u128 allocator model. -/
theorem wide_parts (wide : BitVec 128) (lo hi : BitVec 64)
    (equal : Udivti3.value lo hi = wide.toNat) :
    wide.setWidth 64 = lo ∧ (wide >>> 64).setWidth 64 = hi ∧
      (wide.toNat < 2^64 ↔ hi = 0#64) := by
  have lowBound := lo.isLt
  have highBound := hi.isLt
  have value : wide.toNat = hi.toNat * 2^64 + lo.toNat := by
    simpa only [Udivti3.value, Udivti3.radix] using equal.symm
  refine ⟨BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_, ?_⟩
  · rw [BitVec.toNat_setWidth, value]
    omega
  · rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, value]
    omega
  · constructor
    · intro bound
      have zero : hi.toNat = 0 := by omega
      exact BitVec.eq_of_toNat_eq (by simpa using zero)
    · intro zero
      simp only [zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_mul, Nat.zero_add] at value
      omega

/-- The abstract source's quotient bits equal those returned by the fully
executed runtime callee, without any artificial quotient-fit assumption. -/
theorem wide_quotient_parts (operand : NatOperand) (divisor lo hi : BitVec 64)
    (count : operand.wordCount ≤ 2)
    (quotient : Udivti3.value lo hi = operand.value / divisor.toNat) :
    (SszNative.NatDivision.wideQuotient operand divisor).setWidth 64 = lo ∧
      ((SszNative.NatDivision.wideQuotient operand divisor) >>> 64).setWidth 64 = hi ∧
      ((SszNative.NatDivision.wideQuotient operand divisor).toNat < 2^64 ↔ hi = 0#64) := by
  apply wide_parts
  rw [SszNative.NatDivision.wideQuotient_toNat operand divisor count]
  exact quotient

end SszX86.NatDivision

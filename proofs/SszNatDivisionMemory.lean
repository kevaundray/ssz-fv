import SszNatAddMemory
import SszNatDivision

set_option autoImplicit false

namespace SszNative.NatDivision

/-- The exact quotient representation is owned whenever the original operand
and every allocated quotient limb remain readable, including trimmed high zeros. -/
theorem run_result_at (observe : Nat → Nat → Option Nat)
    (operand : NatOperand) (divisor : BitVec 64) (base capacity used : Nat)
    (result : NatOperand) (remainder : BitVec 64)
    (original : operand.At observe)
    (allocated : ∀ reservation, (run operand divisor base capacity used).allocation = some reservation →
      (NatOperand.large (BitVec.ofNat 64 reservation.pointer)
        (run operand divisor base capacity used).written).At observe)
    (success : (run operand divisor base capacity used).result = .ok (result, remainder)) :
    result.At observe := by
  by_cases zero : divisor = 0
  · simp only [run, zero, ↓reduceIte] at success
    cases success
  · by_cases one : divisor = 1
    · simp only [run, one, ↓reduceIte] at success
      cases success
      exact NatOperand.normalized_at observe operand original
    · by_cases small : operand.wordCount ≤ 2
      · simp only [run, zero, one, small, ↓reduceIte] at success allocated
        cases quotient : (NatArithmetic.fromWide base capacity used
            (wideQuotient operand divisor)).result with
        | error reason =>
          simp only [quotient, Except.map] at success
          cases success
        | ok value =>
          simp only [quotient, Except.map] at success
          cases success
          exact NatArithmetic.fromWide_result_at observe base capacity used _ _ quotient allocated
      · cases reserved : Arena.reserve base capacity used operand.wordCount with
        | none =>
          simp only [run, zero, one, small, ↓reduceIte, reserved] at success
          cases success
        | some reservation =>
          simp only [run, zero, one, small, ↓reduceIte, reserved] at success allocated
          cases success
          exact NatOperand.fromWords_at observe _ _ (allocated reservation rfl)

end SszNative.NatDivision

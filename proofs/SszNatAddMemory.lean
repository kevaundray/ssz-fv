import SszNatOperandNormalization

set_option autoImplicit false

namespace SszNative

namespace NatArithmetic

theorem committed_result_at (observe : Nat → Nat → Option Nat)
    (reservation : Arena.Reservation) (words : List (BitVec 64)) (result : NatOperand)
    (success : (committed reservation words).result = .ok result)
    (stored : (NatOperand.large (BitVec.ofNat 64 reservation.pointer) words).At observe) :
    result.At observe := by
  cases success
  exact NatOperand.fromWords_at observe _ words stored

theorem fromWide_result_at (observe : Nat → Nat → Option Nat)
    (base capacity used : Nat) (wide : BitVec 128) (result : NatOperand)
    (success : (fromWide base capacity used wide).result = .ok result)
    (stored : ∀ reservation, (fromWide base capacity used wide).allocation = some reservation →
      (NatOperand.large (BitVec.ofNat 64 reservation.pointer)
        (fromWide base capacity used wide).written).At observe) : result.At observe := by
  by_cases fits : wide.toNat < 2^64
  · simp only [fromWide, fits, ↓reduceIte] at success
    cases success
    trivial
  · cases reserved : Arena.reserve base capacity used 2 with
    | none =>
      simp only [fromWide, fits, ↓reduceIte, reserved] at success
      cases success
    | some reservation =>
      simp only [fromWide, fits, ↓reduceIte, reserved] at success stored
      exact committed_result_at observe reservation _ result success (stored reservation rfl)

end NatArithmetic

namespace NatAdd

/-- Exact result ownership follows from the original operands and every allocated limb,
including redundant high zero words that normalization does not retain. -/
theorem run_result_at (observe : Nat → Nat → Option Nat)
    (left right : NatOperand) (base capacity used : Nat) (result : NatOperand)
    (leftStored : left.At observe) (rightStored : right.At observe)
    (allocated : ∀ reservation, (run left right base capacity used).allocation = some reservation →
      (NatOperand.large (BitVec.ofNat 64 reservation.pointer)
        (run left right base capacity used).written).At observe)
    (success : (run left right base capacity used).result = .ok result) : result.At observe := by
  by_cases hl : left.wordCount = 0
  · rw [run_zero_left left right base capacity used hl] at success
    cases success
    exact NatOperand.normalized_at observe right rightStored
  · by_cases hr : right.wordCount = 0
    · rw [run_zero_right left right base capacity used hl hr] at success
      cases success
      exact NatOperand.normalized_at observe left leftStored
    · by_cases hs : left.wordCount ≤ 1 ∧ right.wordCount ≤ 1
      · rw [run_one_word left right base capacity used hl hr hs] at success allocated
        exact NatArithmetic.fromWide_result_at observe base capacity used _ result success allocated
      · rw [run_large left right base capacity used hl hr hs] at success allocated
        by_cases fits : count left right + 1 < 2^64
        · simp only [fits, ↓reduceIte] at success allocated
          cases reserved : Arena.reserve base capacity used (count left right + 1) with
          | none =>
            rw [reserved] at success
            cases success
          | some reservation =>
            rw [reserved] at success allocated
            exact NatArithmetic.committed_result_at observe reservation _ result success
              (allocated reservation rfl)
        · simp only [fits, ↓reduceIte] at success
          cases success

end NatAdd
end SszNative

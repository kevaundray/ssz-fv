import SszX86.CodecMeasureFixedArithmeticResources

namespace SszX86.CodecMeasureFixed
open SszNative

theorem mulWord_result_provenance (operand : NatOperand) (factor : BitVec 64)
    (base capacity used : Nat) :
    ArithmeticProvenance (Emit.NatBorrowed operand)
      (SszNative.NatMul.runWord operand factor base capacity used) := by
  by_cases zero : factor = 0
  · subst factor
    rw [SszNative.NatMul.runWord_zero]
    exact unchanged_small_provenance _ _ _
  · by_cases one : factor = 1
    · subst factor
      rw [SszNative.NatMul.runWord_one]
      exact unchanged_normalized_provenance _ _
    · by_cases small : operand.wordCount ≤ 1
      · rw [SszNative.NatMul.runWord_small operand factor base capacity used zero one small]
        exact fromWide_provenance _ _ _ _ _
      · rw [SszNative.NatMul.runWord_large operand factor base capacity used zero one (by omega)]
        split
        · split
          · exact unchanged_error_provenance _ _ _
          · exact committed_provenance _ _ _
        · exact unchanged_error_provenance _ _ _

theorem mul_result_provenance (left right : NatOperand) (base capacity used : Nat) :
    ArithmeticProvenance (fun a => Emit.NatBorrowed left a ∨ Emit.NatBorrowed right a)
      (SszNative.NatMul.run left right base capacity used) := by
  by_cases zero : left.wordCount = 0 ∨ right.wordCount = 0
  · rw [SszNative.NatMul.run_zero left right base capacity used zero]
    exact unchanged_small_provenance _ _ _
  · by_cases rightOne : right.wordCount = 1
    · rw [SszNative.NatMul.run_right_one left right base capacity used (by omega) rightOne]
      exact arithmeticProvenance_mono (mulWord_result_provenance _ _ _ _ _)
        (fun _ => Or.inl)
    · by_cases leftOne : left.wordCount = 1
      · rw [SszNative.NatMul.run_left_one left right base capacity used leftOne
          (by omega) rightOne]
        exact arithmeticProvenance_mono (mulWord_result_provenance _ _ _ _ _)
          (fun _ => Or.inr)
      · rw [SszNative.NatMul.run_large left right base capacity used (by omega) (by omega)]
        split
        · split
          · exact unchanged_error_provenance _ _ _
          · exact committed_provenance _ _ _
        · exact unchanged_error_provenance _ _ _

end SszX86.CodecMeasureFixed

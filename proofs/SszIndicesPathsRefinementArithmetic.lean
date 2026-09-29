import SszIndicesPathsRefinement
import SszIndicesArithmeticSemanticCeil
import SszIndicesArithmeticSemanticConcat
import SszIndicesProgressiveSemantic
import SszIndicesArithmeticShiftPhysical

set_option autoImplicit false

namespace SszNative.Indices

 theorem resourceValue_refines (actual : Outcome NatOperand) (expected : Nat)
    (correct : ∀ result, actual.result = .ok result → result.value = expected)
    (errors : ∀ reason, actual.result = .error reason → reason = scratch) :
    PathRefines NatOperand.value actual.result (.ok expected) := by
  cases returned : actual.result with
  | error reason =>
      rw [errors reason returned]
      exact PathRefines.arithmetic_error _ _ _
  | ok result =>
      rw [← correct result returned]
      exact PathRefines.ok _ _

 theorem ceilShift_path_refines (value : NatOperand) (shift base capacity used : Nat)
    (physical : value.words.length < 2^64) (bounded : shift ≤ 64) :
    PathRefines NatOperand.value (ceilShift value shift base capacity used).result
      (.ok ((value.value + 2^shift - 1) / 2^shift)) := by
  apply resourceValue_refines
  · intro result success
    exact ceilShift_value value shift base capacity used result physical bounded success
  · exact ceilShift_error value shift base capacity used

 theorem rebase_path_refines (value : NatOperand) (bits base capacity used : Nat)
    (physical : value.words.length < 2^64) :
    PathRefines NatOperand.value (rebase value bits base capacity used).result
      (.ok (Ssz.gindexRebase value.value bits)) := by
  apply resourceValue_refines
  · intro result success
    exact rebase_value value bits base capacity used result physical success
  · exact rebase_error value bits base capacity used

 theorem progressiveChunkIndex_path_refines (value : NatOperand) (base capacity used : Nat)
    (physical : value.words.length < 2^64) :
    PathRefines NatOperand.value (progressiveChunkIndex value base capacity used).result
      (.ok (Ssz.progressiveChunkGindex value.value)) := by
  apply resourceValue_refines
  · intro result success
    exact progressiveChunkIndex_value value base capacity used result physical success
  · exact progressiveChunkIndex_error value base capacity used

 theorem concat_path_refines (outer inner : NatOperand) (base capacity used : Nat)
    (outerPhysical : outer.words.length < 2^64) (innerPhysical : inner.words.length < 2^64) :
    PathRefines NatOperand.value (concat outer inner base capacity used).result
      (Ssz.gindexConcat outer.value inner.value) := by
  by_cases outerZero : outer.wordCount = 0
  · have valueZero := (wordCount_zero_iff outer).mp outerZero
    apply PathRefines.of_eq
    simp [concat, checkedDepth, outerZero, unchanged, eraseResult,
      Ssz.gindexConcat, Ssz.gindexDepth, valueZero]
  by_cases innerZero : inner.wordCount = 0
  · have valueZero := (wordCount_zero_iff inner).mp innerZero
    have outerPositive : ¬ outer.value < 1 := by
      have nonzero : outer.value ≠ 0 := fun h => outerZero ((wordCount_zero_iff outer).mpr h)
      omega
    apply PathRefines.of_eq
    simp [concat, checkedDepth, outerZero, innerZero, unchanged, eraseResult,
      Ssz.gindexConcat, Ssz.gindexDepth, valueZero, outerPositive]
  cases returned : (concat outer inner base capacity used).result with
  | ok result =>
      rw [concat_value outer inner base capacity used result outerPhysical innerPhysical returned]
      exact PathRefines.ok _ _
  | error reason =>
      have resource : reason = scratch := by
        simp only [concat, checkedDepth, outerZero, innerZero, ↓reduceIte] at returned
        split at returned
        · cases returned
        · split at returned
          · cases returned
          · split at returned
            · split at returned
              · rename_i failed checked
                cases returned
                exact wordCount_error _ _ checked
              · split at returned
                · exact makeNat_error _ _ _ _ _ _ returned
                · cases returned
                  rfl
            · cases returned
              rfl
      rw [resource]
      exact PathRefines.arithmetic_error _ _ _

end SszNative.Indices

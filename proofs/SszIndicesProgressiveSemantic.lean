import SszIndicesProgressiveSemanticMasks
import SszIndicesArithmeticSemanticMake

set_option autoImplicit false

namespace SszNative.Indices

/-- The optimized borrowed-limb threshold comparison, two-stage subtraction and
OR-mask initializer refine the pinned default-depth/default-spine recursion.
All raw representations are admitted; only actual host storage is physically
bounded, and allocation/checked-width failures remain explicit in the premise. -/
theorem progressiveChunkIndex_value (chunk : NatOperand) (base capacity used : Nat)
    (result : NatOperand) (_physical : chunk.words.length < 2 ^ 64)
    (success : (progressiveChunkIndex chunk base capacity used).result = .ok result) :
    result.value = Ssz.progressiveChunkGindex chunk.value := by
  unfold progressiveChunkIndex at success
  cases thresholdCount : wordCount (depth chunk / 2 * 2 + 1) with
  | error reason => simp [thresholdCount, unchanged] at success
  | ok thresholdWords =>
      simp only [thresholdCount] at success
      have interval := ProgressiveSemantic.progressiveDepth_interval chunk thresholdWords
        (wordCount_covers _ _ thresholdCount)
      dsimp only at interval
      split at success
      · split at success
        · rename_i leadingFits
          cases outputCount : wordCount
              (progressiveDepth chunk thresholdWords + progressiveDepth chunk thresholdWords / 2 + 2 + 1) with
          | error reason => simp [outputCount, unchanged] at success
          | ok words =>
              simp only [outputCount] at success
              have enough := wordCount_covers _ _ outputCount
              have value := makeNatState_success_value words base capacity used false
                (progressiveStep chunk (progressiveDepth chunk thresholdWords)) result success
              rw [value, interval.1]
              apply ProgressiveSemantic.fillWords_value chunk
                (progressiveDepth chunk thresholdWords / 2) words interval.2.1 interval.2.2
              omega
        · simp [unchanged] at success
      · simp [unchanged] at success

end SszNative.Indices

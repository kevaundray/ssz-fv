import SszIndicesProgressive
import SszIndicesArithmeticResources

set_option autoImplicit false

namespace SszNative.Indices

theorem progressiveChunkIndex_cursor_bounds (chunk : NatOperand) (base capacity used : Nat)
    (valid : Arena.Valid base capacity used) :
    used ≤ (progressiveChunkIndex chunk base capacity used).used ∧
      (progressiveChunkIndex chunk base capacity used).used ≤ capacity := by
  unfold progressiveChunkIndex
  dsimp only
  split
  · exact ⟨Nat.le_refl _, valid.2.2.2⟩
  · split
    · split
      · split
        · exact ⟨Nat.le_refl _, valid.2.2.2⟩
        · exact makeNatState_cursor_bounds _ _ _ _ _ _ valid
      · exact ⟨Nat.le_refl _, valid.2.2.2⟩
    · exact ⟨Nat.le_refl _, valid.2.2.2⟩

theorem progressiveChunkIndex_used_mono (chunk : NatOperand) (base capacity used : Nat) :
    used ≤ (progressiveChunkIndex chunk base capacity used).used := by
  unfold progressiveChunkIndex
  dsimp only
  split
  · exact Nat.le_refl _
  · split
    · split
      · split
        · exact Nat.le_refl _
        · exact makeNatState_used_mono _ _ _ _ _ _
      · exact Nat.le_refl _
    · exact Nat.le_refl _

theorem progressiveChunkIndex_atomic (chunk : NatOperand) (base capacity used : Nat) :
    Atomic used (progressiveChunkIndex chunk base capacity used) := by
  unfold progressiveChunkIndex
  dsimp only
  split
  · exact unchanged_atomic _ _
  · split
    · split
      · split
        · exact unchanged_atomic _ _
        · exact makeNatState_atomic _ _ _ _ _ _
      · exact unchanged_atomic _ _
    · exact unchanged_atomic _ _

end SszNative.Indices

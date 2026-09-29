import SszIndicesCore
import Ssz.Proofs.Merkle.ProgressiveLevels

set_option autoImplicit false

namespace SszNative.Indices.ProgressiveSemantic

/-- The actual threshold of level `level`, without a logical metadata cap. -/
def offset (level : Nat) : Nat := (4 ^ level - 1) / 3

theorem offset_eq_levelStart (level : Nat) : offset level = Ssz.levelStart level := by
  have capacity := Ssz.levelStart_capacity level
  unfold offset
  omega

theorem offset_succ (level : Nat) : offset (level + 1) = offset level + 4 ^ level := by
  simp only [offset_eq_levelStart, Ssz.levelStart_succ]

theorem offset_capacity (level : Nat) : 3 * offset level + 1 = 4 ^ level := by
  simpa only [offset_eq_levelStart] using Ssz.levelStart_capacity level

theorem width_eq (level : Nat) : 4 ^ level = 2 ^ (2 * level) := by
  rw [Nat.pow_mul]

theorem offset_boundaries : offset 0 = 0 ∧ offset 1 = 1 ∧
    offset 2 = 5 ∧ offset 3 = 21 := by decide


theorem offset_peel (level : Nat) : offset (level + 1) = 1 + 4 * offset level := by
  simpa only [offset_eq_levelStart] using Ssz.levelStart_peel level

theorem offset_testBit (level position : Nat) :
    (offset level).testBit position = decide (position < 2 * level ∧ position % 2 = 0) := by
  induction level generalizing position with
  | zero => simp [offset]
  | succ level ih =>
    rw [offset_peel, Nat.add_comm]
    change (2 ^ 2 * offset level + 1).testBit position = _
    rw [Nat.testBit_two_pow_mul_add _ (by decide : 1 < 2 ^ 2)]
    by_cases low : position < 2
    · have cases : position = 0 ∨ position = 1 := by omega
      rcases cases with rfl | rfl <;> simp <;> decide
    · simp only [low, ↓reduceIte]
      rw [ih]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      omega

/-- With initial spine 2 the spine is `3*2^level-1`, not `2^(level+1)-1`.
The latter already gives the wrong initial spine at level zero. -/
def spine (level : Nat) : Nat := 3 * 2 ^ level - 1

theorem spine_zero : spine 0 = 2 := rfl

theorem spine_succ (level : Nat) : spine (level + 1) = spine level * 2 + 1 := by
  have positive : 1 ≤ 2 ^ level := Nat.one_le_two_pow
  simp only [spine, Nat.pow_succ]
  omega

/-- The numeric value of the two disjoint upper mask ranges. -/
def upperMasks (level : Nat) : Nat :=
  2 ^ (2 * level + level + 2) + (2 ^ level - 1) * 2 ^ (2 * level + 1)

theorem upperMasks_eq (level : Nat) :
    upperMasks level = spine level * 2 * 4 ^ level := by
  have positive : 1 ≤ 2 ^ level := Nat.one_le_two_pow
  have high : 2 ^ (2 * level + level + 2) = 4 * 2 ^ level * 4 ^ level := by
    rw [Nat.pow_add, Nat.pow_add, ← width_eq]
    simp only [Nat.pow_succ, Nat.pow_zero]
    grind
  have middle : 2 ^ (2 * level + 1) = 2 * 4 ^ level := by
    rw [Nat.pow_add, ← width_eq]
    simp [Nat.mul_comm]
  simp only [upperMasks, high, middle, spine]
  generalize h : 2 ^ level = power at positive ⊢
  obtain ⟨n, rfl⟩ : ∃ n, power = n + 1 := ⟨power - 1, by omega⟩
  grind

/-- The vendor recursion at any selected half-open progressive interval. -/
theorem closed_of_interval (chunk level : Nat)
    (lower : offset level ≤ chunk) (upper : chunk < offset (level + 1)) :
    Ssz.progressiveChunkGindex chunk = upperMasks level + (chunk - offset level) := by
  have inside : chunk - offset level < 4 ^ level := by
    rw [offset_succ] at upper
    omega
  have closed := Ssz.progressiveChunkGindex_level level (chunk - offset level) inside
  rw [← offset_eq_levelStart, Nat.add_sub_of_le lower] at closed
  simpa only [upperMasks_eq, spine] using closed

/-- The source's log-based candidate can skip at most one threshold. -/
theorem candidate_interval (chunk : Nat) :
    offset (chunk.log2 / 2) ≤ chunk ∧ chunk < offset (chunk.log2 / 2 + 2) := by
  by_cases zero : chunk = 0
  · subst chunk
    decide
  · have floor := Nat.log2_self_le zero
    have ceiling := Nat.lt_log2_self (n := chunk)
    have lowerPower : 2 ^ (2 * (chunk.log2 / 2)) ≤ 2 ^ chunk.log2 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have upperPower : 2 ^ (chunk.log2 + 1) ≤ 4 ^ (chunk.log2 / 2 + 1) := by
      rw [width_eq]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have lowerCapacity := offset_capacity (chunk.log2 / 2)
    have upperCapacity := offset_capacity (chunk.log2 / 2 + 1)
    have lowerWidth := width_eq (chunk.log2 / 2)
    have next : offset (chunk.log2 / 2 + 2) =
        offset (chunk.log2 / 2 + 1) + 4 ^ (chunk.log2 / 2 + 1) := by
      simpa only [Nat.add_assoc] using offset_succ (chunk.log2 / 2 + 1)
    constructor
    · omega
    · omega

/-- The single optimized threshold comparison determines the recursive level. -/
theorem selected_interval (chunk : Nat) :
    let candidate := chunk.log2 / 2
    let selected := if chunk < offset (candidate + 1) then candidate else candidate + 1
    offset selected ≤ chunk ∧ chunk < offset (selected + 1) := by
  have bounds := candidate_interval chunk
  dsimp only
  split
  · rename_i below
    exact ⟨bounds.1, below⟩
  · rename_i above
    exact ⟨by omega, by simpa only [Nat.add_assoc] using bounds.2⟩

end SszNative.Indices.ProgressiveSemantic

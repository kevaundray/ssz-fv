import SszProofTraversalWindowRefinement
import Ssz.Proofs.Merkle.Gindex

set_option autoImplicit false

namespace SszNative.Proof

/-- Rebasing changes no consumed low path bit. -/
theorem rebase_below (index full depth : Nat) (inside : depth ≤ full) :
    Ssz.gindexBelow (Ssz.gindexRebase index full) depth = Ssz.gindexBelow index depth := by
  have divides := Nat.pow_dvd_pow 2 inside
  simp only [Ssz.gindexRebase, Ssz.gindexBelow, Nat.add_mod,
    Nat.mod_eq_zero_of_dvd divides, Nat.zero_add, Nat.mod_mod_of_dvd _ divides, Nat.mod_mod]

theorem rebase_rebase (index full depth : Nat) (inside : depth ≤ full) :
    Ssz.gindexRebase (Ssz.gindexRebase index full) depth = Ssz.gindexRebase index depth := by
  change 2 ^ depth + Ssz.gindexBelow (Ssz.gindexRebase index full) depth =
    2 ^ depth + Ssz.gindexBelow index depth
  exact congrArg (fun below => 2 ^ depth + below) (rebase_below index full depth inside)

theorem rebase_bit (index full position : Nat) (inside : position < full) :
    Ssz.gindexBit (Ssz.gindexRebase index full) position = Ssz.gindexBit index position := by
  have same := congrArg (fun value => value.testBit position) (rebase_below index full full (Nat.le_refl _))
  simpa only [Ssz.gindexBelow, Nat.testBit_mod_two_pow, inside, decide_true,
    Bool.true_and, Ssz.gindexBit] using same

theorem rebase_window (index full offset width : Nat) (inside : offset + width ≤ full) :
    ((Ssz.gindexRebase index full) / 2 ^ offset) % 2 ^ width =
      (index / 2 ^ offset) % 2 ^ width := by
  apply Nat.eq_of_testBit_eq
  intro position
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases selected : position < width
  · simp only [selected, decide_true, Bool.true_and]
    exact rebase_bit index full (position + offset) (by omega)
  · simp only [selected, decide_false, Bool.false_and]

theorem rebase_depth (index depth : Nat) : (Ssz.gindexRebase index depth).log2 = depth := by
  have positive := Nat.two_pow_pos depth
  have below := Nat.mod_lt index positive
  apply (Nat.log2_eq_iff (by unfold Ssz.gindexRebase; omega)).mpr
  simp only [Ssz.gindexRebase, Ssz.gindexBelow, Nat.pow_succ]
  omega

theorem rebase_positive (index depth : Nat) : 0 < Ssz.gindexRebase index depth := by
  have positive := Nat.two_pow_pos depth
  simp only [Ssz.gindexRebase]
  omega

theorem rebase_self (index : Nat) (positive : 0 < index) :
    Ssz.gindexRebase index index.log2 = index := by
  obtain ⟨lower, upper⟩ := Ssz.gindexDepth_bounds (by omega : 1 ≤ index)
  have remainder : index % 2 ^ index.log2 = index - 2 ^ index.log2 := by
    rw [Nat.mod_eq_sub_mod lower, Nat.mod_eq_of_lt (by
      simp only [Nat.pow_succ] at upper
      omega : index - 2 ^ index.log2 < 2 ^ index.log2)]
  simp only [Ssz.gindexRebase, Ssz.gindexBelow, remainder]
  omega

theorem physicalOffset_eq (base position span : Nat) :
    physicalOffset base position span = physicalIndex (base + position * span) := by
  unfold physicalOffset physicalIndex
  by_cases product : position * span < 2 ^ 64
  · simp only [product, ↓reduceIte]
    rfl
  · have total : ¬base + position * span < 2 ^ 64 := by omega
    simp only [product, total, ↓reduceIte]
    rfl

/-- Exact checked-origin correspondence. Failure names an interval past every
physical leaf, not an invalid logical generalized index. -/
theorem boundedStart_eq (index : NatOperand) (depth base spanDepth : Nat)
    (physical : index.words.length < 2 ^ 64) (baseFits : base < 2 ^ 64) :
    boundedStart index depth base spanDepth =
      physicalIndex (base + (index.value % 2 ^ depth) * 2 ^ spanDepth) := by
  rw [boundedStart, window_eq index 0 depth physical]
  simp only [Nat.pow_zero, Nat.div_one]
  by_cases huge : 64 ≤ spanDepth
  · simp only [huge, ↓reduceIte]
    have power : 2 ^ 64 ≤ 2 ^ spanDepth := Nat.pow_le_pow_right (by decide) huge
    by_cases zero : index.value % 2 ^ depth = 0
    · simp [zero, physicalIndex, baseFits]
    · have product : 2 ^ 64 ≤ (index.value % 2 ^ depth) * 2 ^ spanDepth := by
        have scaled := Nat.mul_le_mul_right (2 ^ spanDepth) (by omega : 1 ≤ index.value % 2 ^ depth)
        simp only [Nat.one_mul] at scaled
        omega
      by_cases fits : index.value % 2 ^ depth < 2 ^ 64
      · simp [fits, zero, physicalIndex, show ¬base + (index.value % 2 ^ depth) * 2 ^ spanDepth < 2 ^ 64 by omega]
      · simp [fits, physicalIndex, show ¬base + (index.value % 2 ^ depth) * 2 ^ spanDepth < 2 ^ 64 by omega]
  · simp only [huge, ↓reduceIte]
    by_cases fits : index.value % 2 ^ depth < 2 ^ 64
    · simp only [fits, ↓reduceIte, Option.bind_some, physicalOffset_eq]
    · have scaled := Nat.mul_le_mul_left (index.value % 2 ^ depth)
        (by have := Nat.two_pow_pos spanDepth; omega : 1 ≤ 2 ^ spanDepth)
      simp only [Nat.mul_one] at scaled
      have total : ¬base + (index.value % 2 ^ depth) * 2 ^ spanDepth < 2 ^ 64 := by omega
      simp [fits, physicalIndex, total]

theorem boundedStop_eq (count start spanDepth : Nat) (physical : count < 2 ^ 64) :
    boundedStop count start spanDepth = min (start + 2 ^ spanDepth) count := by
  unfold boundedStop
  split
  · rename_i huge
    have power := Nat.pow_le_pow_right (by decide : 0 < 2) huge
    omega
  · omega

/-- The exact geometric spine invariant also proves every active source u128
addition and multiplication safe from the physical leaf bound. -/
def SpineInvariant (start capacity : Nat) : Prop := capacity = 3 * start + 1

theorem spineInvariant_initial : SpineInvariant 0 1 := rfl

theorem spineInvariant_step (start capacity : Nat) (valid : SpineInvariant start capacity) :
    SpineInvariant (start + capacity) (capacity * 4) := by
  unfold SpineInvariant at *
  omega

theorem spine_active_u128 (count start capacity : Nat)
    (physical : count < 2 ^ 64) (active : start < count) (valid : SpineInvariant start capacity) :
    start < 2 ^ 64 ∧ start + capacity < 2 ^ 128 ∧ capacity * 4 < 2 ^ 128 := by
  unfold SpineInvariant at valid
  omega

end SszNative.Proof

import SszIndicesArithmeticResources
import SszNatShiftResources

set_option autoImplicit false

namespace SszNative.Indices

theorem below_cursor_bounds (index : NatOperand) (bits base capacity used : Nat)
    (valid : Arena.Valid base capacity used) :
    used ≤ (below index bits base capacity used).used ∧
      (below index bits base capacity used).used ≤ capacity := by
  unfold below
  split
  · exact ⟨Nat.le_refl _, valid.2.2.2⟩
  · split
    · exact ⟨Nat.le_refl _, valid.2.2.2⟩
    · exact makeNat_cursor_bounds _ _ _ _ _ valid

theorem sibling_cursor_bounds (index : NatOperand) (base capacity used : Nat)
    (valid : Arena.Valid base capacity used) :
    used ≤ (sibling index base capacity used).used ∧
      (sibling index base capacity used).used ≤ capacity :=
  shiftXor_cursor_bounds index 0 true base capacity used valid

theorem parent_cursor_bounds (index : NatOperand) (base capacity used : Nat)
    (valid : Arena.Valid base capacity used) :
    used ≤ (parent index base capacity used).used ∧
      (parent index base capacity used).used ≤ capacity :=
  NatShift.shr_cursor_bounds index 1 base capacity used valid

theorem child_cursor_bounds (index : NatOperand) (right : Bool) (base capacity used : Nat)
    (valid : Arena.Valid base capacity used) :
    used ≤ (child index right base capacity used).used ∧
      (child index right base capacity used).used ≤ capacity := by
  unfold child
  split
  · exact ⟨Nat.le_refl _, valid.2.2.2⟩
  · split
    · split
      · exact ⟨Nat.le_refl _, valid.2.2.2⟩
      · exact makeNat_cursor_bounds _ _ _ _ _ valid
    · exact ⟨Nat.le_refl _, valid.2.2.2⟩

theorem concat_cursor_bounds (outer inner : NatOperand) (base capacity used : Nat)
    (valid : Arena.Valid base capacity used) :
    used ≤ (concat outer inner base capacity used).used ∧
      (concat outer inner base capacity used).used ≤ capacity := by
  unfold concat
  split
  · exact ⟨Nat.le_refl _, valid.2.2.2⟩
  · split
    · exact ⟨Nat.le_refl _, valid.2.2.2⟩
    · split
      · exact ⟨Nat.le_refl _, valid.2.2.2⟩
      · split
        · exact ⟨Nat.le_refl _, valid.2.2.2⟩
        · split
          · split
            · exact ⟨Nat.le_refl _, valid.2.2.2⟩
            · split
              · exact makeNat_cursor_bounds _ _ _ _ _ valid
              · exact ⟨Nat.le_refl _, valid.2.2.2⟩
          · exact ⟨Nat.le_refl _, valid.2.2.2⟩

theorem rebase_cursor_bounds (index : NatOperand) (bits base capacity used : Nat)
    (valid : Arena.Valid base capacity used) :
    used ≤ (rebase index bits base capacity used).used ∧
      (rebase index bits base capacity used).used ≤ capacity := by
  unfold rebase
  split
  · split
    · exact ⟨Nat.le_refl _, valid.2.2.2⟩
    · exact makeNat_cursor_bounds _ _ _ _ _ valid
  · exact ⟨Nat.le_refl _, valid.2.2.2⟩

theorem nextPow2_cursor_bounds (count : NatOperand) (base capacity used : Nat)
    (valid : Arena.Valid base capacity used) :
    used ≤ (nextPow2 count base capacity used).used ∧
      (nextPow2 count base capacity used).used ≤ capacity := by
  unfold nextPow2
  split
  · exact ⟨Nat.le_refl _, valid.2.2.2⟩
  · split
    · exact ⟨Nat.le_refl _, valid.2.2.2⟩
    · exact NatShift.shl_cursor_bounds _ _ _ _ _ valid

theorem ceilShift_cursor_bounds (value : NatOperand) (shift base capacity used : Nat)
    (valid : Arena.Valid base capacity used) :
    used ≤ (ceilShift value shift base capacity used).used ∧
      (ceilShift value shift base capacity used).used ≤ capacity := by
  unfold ceilShift
  split
  · exact NatShift.shr_cursor_bounds _ _ _ _ _ valid
  · split
    · exact ⟨Nat.le_refl _, valid.2.2.2⟩
    · exact ⟨Nat.le_refl _, valid.2.2.2⟩
    · split
      · split
        · exact makeNatState_cursor_bounds _ _ _ _ _ _ valid
        · exact ⟨Nat.le_refl _, valid.2.2.2⟩
      · exact makeNatState_cursor_bounds _ _ _ _ _ _ valid

end SszNative.Indices

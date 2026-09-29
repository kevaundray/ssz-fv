import SszHashLayout
import SszHashLayoutDomain

set_option autoImplicit false

namespace SszNative.HashLayout

open Codec (Desc Value)

def Layout.Generated (desc : Desc) (value : Value) (view : Layout) : Prop :=
  match view.leaves with
  | .packed _ => True
  | .nested nested => SszNative.HashLayout.Generated desc value nested

/-- Provenance is derived from the source constructor branch, including the
actual first-match union lookup. It does not require successful descendants. -/
theorem layout_generated (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (view : Layout) (success : (layout desc value arena).result = .ok view) :
    view.Generated desc value := by
  cases desc with
  | primitive shape =>
      cases shape <;> cases value <;>
        simp only [layout, lift, bind, unchanged] at success
      repeat' first | split at success | cases success
      all_goals exact True.intro
  | vector element length =>
      cases value <;> simp only [layout, sequence, lift, bind, unchanged] at success
      repeat' first | split at success | cases success
      all_goals first | exact True.intro | exact Generated.vector _ _ _
  | list element limit =>
      cases value <;> simp only [layout, sequence, lift, bind, unchanged] at success
      repeat' first | split at success | cases success
      all_goals first | exact True.intro | exact Generated.list _ _ _
  | progressiveList element limit =>
      cases value <;> simp only [layout, sequence, lift, bind, unchanged] at success
      repeat' first | split at success | cases success
      all_goals first | exact True.intro | exact Generated.progressiveList _ _ _
  | container fields =>
      cases value <;> simp only [layout, unchanged] at success
      repeat' first | split at success | cases success
      all_goals exact Generated.container _ _
  | progressiveContainer active fields =>
      cases value <;> simp only [layout, unchanged] at success
      repeat' first | split at success | cases success
      all_goals exact Generated.progressiveContainer _ _ _
  | compatibleUnion options =>
      cases value <;> simp only [layout, unchanged] at success
      all_goals
        repeat first | split at success | cases success
      all_goals exact Generated.compatibleUnion _ _ _ _ (by assumption)

theorem Layout.Generated.at_child (desc : Desc) (input : Value) (view : Layout)
    (generated : view.Generated desc input) (index : Nat) (childDesc : Desc) (child : Value)
    (selected : view.nested index = some (childDesc, child)) : child ∈ input.children := by
  cases leafEq : view.leaves with
  | packed packed => simp only [Layout.nested, leafEq] at selected; cases selected
  | nested nested =>
      have source : SszNative.HashLayout.Generated desc input nested := by
        simpa only [Layout.Generated, leafEq] using generated
      exact source.at_child (by simpa only [Layout.nested, leafEq] using selected)

end SszNative.HashLayout

import SszHashLayoutRootRefinement

set_option autoImplicit false

namespace SszNative.HashLayout

open Codec (Desc Value)

private theorem take_one_drop {α : Type} (values : List α) (index : Nat)
    (inside : index < values.length) :
    (values.drop index).take 1 = [values[index]'inside] := by
  induction values generalizing index with
  | nil => simp at inside
  | cons first rest ih =>
      cases index with
      | zero => rfl
      | succ index =>
          simpa only [List.drop_succ_cons, List.getElem_cons_succ] using
            ih index (by simpa using inside)

private theorem extract_singleton (chunks : Array Ssz.Bytes) (index : Nat)
    (inside : index < chunks.size) :
    chunks.extract index (index + 1) = #[chunks[index]'inside] := by
  apply Array.ext
  · simp only [Array.size_extract, Array.size_singleton]
    omega
  · intro offset left right
    have zero : offset = 0 := by simp only [Array.size_singleton] at right; omega
    subst offset
    simp

/-- A public in-range indexed request is exactly the pinned one-leaf range,
including a recursive child error rather than a successful future-root premise. -/
theorem layoutChunksAt_singleton (budget : Nat) (view : Ssz.MerkleLayout)
    (index : Nat) (inside : index < view.leaves.count) :
    Ssz.layoutChunksAt budget view index (some (index + 1)) =
      (specLeaf budget view index).map (fun root => #[root]) := by
  cases view with
  | mk leaves limit mixin =>
      cases leaves with
      | packed chunks =>
          have bound : index < chunks.size := inside
          simp only [Ssz.layoutChunksAt, specLeaf, extract_singleton chunks index bound,
            Array.getElem?_eq_getElem bound, Option.getD_some, Except.map] <;> rfl
      | nested slots =>
          have bound : index < slots.length := inside
          simp only [Ssz.layoutChunksAt, Nat.add_sub_cancel_left, take_one_drop slots index bound,
            specLeaf, List.getElem?_eq_getElem bound, Option.getD_some]
          cases slot : slots[index] with
          | none => rfl
          | some pair =>
              rcases pair with ⟨desc, value⟩
              simp only [List.mapM_cons, List.mapM_nil]
              cases rootEq : Ssz.hashTreeRootAt budget desc value <;> rfl

/-- Concrete indexed recursion obtains its child refinements from the proved
structural root theorem. The layout success premise describes an already-built
borrowed view, not a future child/root or sufficient scratch assumption. -/
theorem indexedRoot_refines (desc : Desc) (value : Value)
    (layoutArena arena : Delimited.ArenaState) (view : Layout) (index budget : Nat)
    (safe : SafeWidths desc) (descPhysical : desc.Physical) (valuePhysical : value.Physical)
    (laidOut : (layout desc value layoutArena).result = .ok view)
    (enough : desc.nesting ≤ budget + 1) :
    ∃ expected, Ssz.merkleLayout desc.erase value.erase = .ok expected ∧
      Refines Eq (indexedRoot view index arena) (specLeaf budget expected index) := by
  obtain ⟨expected, layoutEq, related⟩ :=
    layout_success desc value layoutArena safe descPhysical valuePhysical view laidOut
  refine ⟨expected, layoutEq, ?_⟩
  apply leafRoot_refines view expected related budget index arena
  intro childDesc child selected cursor
  have origin := layout_generated desc value layoutArena view laidOut
  obtain ⟨childSafe, childDescPhysical, childPhysical, smaller⟩ :=
    layout_child_domain desc value view origin safe descPhysical valuePhysical
      index childDesc child selected
  exact hashTreeRootAt_refines childDesc child cursor budget childSafe childDescPhysical
    childPhysical (by omega)

/-- Indexed leaf_root against pinned layoutChunksAt, with recursive induction
already discharged and a single successful 32-byte node on the right. -/
theorem indexedRoot_layoutChunksAt (desc : Desc) (value : Value)
    (layoutArena arena : Delimited.ArenaState) (view : Layout) (index budget : Nat)
    (safe : SafeWidths desc) (descPhysical : desc.Physical) (valuePhysical : value.Physical)
    (laidOut : (layout desc value layoutArena).result = .ok view)
    (enough : desc.nesting ≤ budget + 1) (inside : index < view.count) :
    ∃ expected, Ssz.merkleLayout desc.erase value.erase = .ok expected ∧
      Refines (fun root chunks => chunks = #[root]) (indexedRoot view index arena)
        (Ssz.layoutChunksAt budget expected index (some (index + 1))) := by
  obtain ⟨expected, layoutEq, refined⟩ := indexedRoot_refines desc value layoutArena arena
    view index budget safe descPhysical valuePhysical laidOut enough
  obtain ⟨expected', layoutEq', related⟩ :=
    layout_success desc value layoutArena safe descPhysical valuePhysical view laidOut
  have same : expected' = expected := by rw [layoutEq] at layoutEq'; exact (Except.ok.inj layoutEq').symm
  subst expected'
  refine ⟨expected, layoutEq, ?_⟩
  rw [layoutChunksAt_singleton budget expected index (by
    rw [← LayoutRefines.count view expected related]; exact inside)]
  exact ResultRefines.map_expected Eq (fun root chunks => chunks = #[root])
    (indexedRoot view index arena).result (specLeaf budget expected index)
    (fun root => #[root]) refined (by intro left right equal; cases equal; rfl)

end SszNative.HashLayout

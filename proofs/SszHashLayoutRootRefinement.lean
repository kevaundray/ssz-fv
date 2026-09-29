import SszHashLayoutRoot
import SszHashLayoutRefinement
import SszHashLayoutStreamRefinement
import SszHashLayoutPhysical
import SszHashLayoutWidths

set_option autoImplicit false

namespace SszNative.HashLayout

open Codec (Desc Value)

theorem layout_child_domain (desc : Desc) (value : Value) (view : Layout)
    (generated : view.Generated desc value) (safe : SafeWidths desc)
    (descPhysical : desc.Physical) (valuePhysical : value.Physical)
    (index : Nat) (childDesc : Desc) (child : Value)
    (selected : view.nested index = some (childDesc, child)) :
    SafeWidths childDesc ∧ childDesc.Physical ∧ child.Physical ∧
      childDesc.nesting < desc.nesting := by
  cases leavesEq : view.leaves with
  | packed packed => simp only [Layout.nested, leavesEq] at selected; cases selected
  | nested nested =>
      have origin : Generated desc value nested := by
        simpa only [Layout.Generated, leavesEq] using generated
      have chosen : nested.at index = some (childDesc, child) := by
        simpa only [Layout.nested, leavesEq] using selected
      have physical := origin.at_physical descPhysical valuePhysical chosen
      exact ⟨origin.at_safeWidths safe chosen, physical.1, physical.2,
        origin.at_nesting_lt chosen⟩

private def evaluateLayout (budget : Nat) (view : Ssz.MerkleLayout) : Except Ssz.Err Ssz.Bytes := do
  let chunks ← Ssz.layoutChunksAt budget view
  let root ← match view.limit with
    | none => .ok (Ssz.merkleizeProgressive chunks.toList)
    | some capacity => Ssz.merkleizeBounded chunks (some capacity)
  return mixRoot view.mixin root

private theorem streamSpec_layout (budget : Nat) (actual : Layout) (expected : Ssz.MerkleLayout)
    (related : LayoutRefines actual expected) :
    streamSpec (specLeaf budget expected) actual.count 0 #[] actual.limit = (do
      let chunks ← Ssz.layoutChunksAt budget expected
      match expected.limit with
      | none => .ok (Ssz.merkleizeProgressive chunks.toList)
      | some capacity => Ssz.merkleizeBounded chunks (some capacity)) := by
  rw [streamSpec_collect, LayoutRefines.count actual expected related]
  have collected := collect_layout budget expected
  cases chunksEq : collect (specLeaf budget expected) expected.leaves.count 0 with
  | error reason =>
      simp only [chunksEq, Except.map] at collected
      rw [← collected]
      rfl
  | ok chunks =>
      simp only [chunksEq, Except.map] at collected
      rw [← collected]
      change mathematicalRoot (#[] ++ chunks.toArray) actual.limit =
        match expected.limit with
        | none => .ok (Ssz.merkleizeProgressive chunks.toArray.toList)
        | some capacity => Ssz.merkleizeBounded chunks.toArray (some capacity)
      rw [Array.empty_append]
      rw [← related.2.1]
      cases actual.limit <;> rfl

private theorem rooted_layout_refines (actual : Layout) (expected : Ssz.MerkleLayout)
    (related : LayoutRefines actual expected) (budget : Nat) (arena : Delimited.ArenaState)
    (physical : actual.count < 2 ^ 64)
    (visit : (index : Nat) → (desc : Desc) → (value : Value) →
      actual.nested index = some (desc, value) → Delimited.ArenaState → Outcome Ssz.Bytes)
    (children : ∀ index desc value selected cursor,
      Refines Eq (visit index desc value selected cursor)
        (Ssz.hashTreeRootAt budget desc.erase value.erase)) :
    Refines Eq
      (bind (stream (fun index cursor => leafRoot actual index cursor (visit index))
        actual.count 0 (TreeState.new actual.limit) arena)
        (fun root used => unchanged used (.ok (mixRoot actual.mixin root))))
      (evaluateLayout budget expected) := by
  have bound : (#[] : Array Ssz.Bytes).size + actual.count ≤ MerkleAccumulator.maxCount := by
    simp only [Array.size_empty, Nat.zero_add, MerkleAccumulator.maxCount,
      MerkleAccumulator.treeLevels]
    omega
  have rooted := stream_refines
    (fun index cursor => leafRoot actual index cursor (visit index))
    (specLeaf budget expected) actual.count 0 (TreeState.new actual.limit) #[] arena
    (TreeState.new_invariant actual.limit) bound
    (fun index cursor => leafRoot_refines actual expected related budget index cursor
      (visit index) (children index))
  have limit : (TreeState.new actual.limit).limit = actual.limit := by
    cases actual.limit <;> rfl
  rw [limit, streamSpec_layout budget actual expected related] at rooted
  have evaluation : evaluateLayout budget expected =
      ((do
        let chunks ← Ssz.layoutChunksAt budget expected
        match expected.limit with
        | none => .ok (Ssz.merkleizeProgressive chunks.toList)
        | some capacity => Ssz.merkleizeBounded chunks (some capacity)) >>=
        fun root => .ok (mixRoot expected.mixin root)) := by
    unfold evaluateLayout
    cases chunksEq : Ssz.layoutChunksAt budget expected <;> cases expected.limit <;> rfl
  rw [evaluation]
  apply ResultRefines.bind Eq Eq _ _ _ _ rooted
  intro actualRoot expectedRoot same used
  subst expectedRoot
  rw [related.2.2]
  exact .ok _ _ rfl

/-- The callback induction interface is private; public rooting assumes only
source-supported domains and structural nesting, not any future child result. -/
private theorem rootStep_refines (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (budget : Nat) (safe : SafeWidths desc) (descPhysical : desc.Physical)
    (valuePhysical : value.Physical) (enough : desc.nesting ≤ budget + 1)
    (visit : Visit value)
    (children : ∀ child (member : child ∈ value.children) childDesc cursor,
      SafeWidths childDesc → childDesc.Physical → child.Physical → childDesc.nesting ≤ budget →
      Refines Eq (visit child member childDesc cursor)
        (Ssz.hashTreeRootAt budget childDesc.erase child.erase)) :
    Refines Eq (rootStep desc value arena visit)
      (Ssz.hashTreeRootAt (budget + 1) desc.erase value.erase) := by
  have layoutRefined := layout_refines desc value arena safe descPhysical valuePhysical
  unfold Refines at layoutRefined
  cases nativeEq : (layout desc value arena).result with
  | error reason =>
      have rootError : (rootStep desc value arena visit).result = .error reason := by
        simp only [rootStep]
        split <;> simp_all
      cases expectedEq : Ssz.merkleLayout desc.erase value.erase with
      | error fault =>
          rw [nativeEq, expectedEq] at layoutRefined
          cases layoutRefined with
          | exhausted expected =>
              change ResultRefines Eq (rootStep desc value arena visit).result _
              rw [rootError]
              exact .exhausted _
          | error actual expected same =>
              change ResultRefines Eq (rootStep desc value arena visit).result _
              rw [rootError]
              simp only [Ssz.hashTreeRootAt, expectedEq]
              exact .error _ _ same
      | ok expected =>
          rw [nativeEq, expectedEq] at layoutRefined
          cases layoutRefined with
          | exhausted expected =>
              change ResultRefines Eq (rootStep desc value arena visit).result _
              rw [rootError]
              exact .exhausted _
  | ok actual =>
      cases expectedEq : Ssz.merkleLayout desc.erase value.erase with
      | error fault =>
          rw [nativeEq, expectedEq] at layoutRefined
          cases layoutRefined
      | ok expected =>
          rw [nativeEq, expectedEq] at layoutRefined
          cases layoutRefined with
          | ok actual expected related =>
              have origin := layout_generated desc value arena actual nativeEq
              have physical := layout_count_physical desc value arena actual
                descPhysical valuePhysical nativeEq
              have refined := rooted_layout_refines actual expected related budget
                { arena with used := (layout desc value arena).used } physical
                (fun index childDesc child selected cursor =>
                  visit child
                    (Layout.Generated.at_child desc value actual origin index childDesc child selected)
                    childDesc cursor)
                (by
                  intro index childDesc child selected cursor
                  obtain ⟨safeChild, physicalDesc, physicalValue, smaller⟩ :=
                    layout_child_domain desc value actual origin safe descPhysical valuePhysical
                      index childDesc child selected
                  exact children child _ childDesc cursor safeChild physicalDesc physicalValue (by omega))
              change ResultRefines Eq (rootStep desc value arena visit).result _
              simp only [rootStep]
              split
              · simp_all
              · rename_i view selected
                have same : view = actual := Except.ok.inj (selected.symm.trans nativeEq)
                subst view
                simp only [Ssz.hashTreeRootAt, expectedEq]
                exact refined

/-- Complete recursive refinement. The pinned budget is sufficient by generated
strict descriptor descent; execution itself recurses on structural values and
has no fuel parameter or exhaustion branch. -/
theorem hashTreeRootAt_refines (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (budget : Nat) (safe : SafeWidths desc) (descPhysical : desc.Physical)
    (valuePhysical : value.Physical) (enough : desc.nesting ≤ budget) :
    Refines Eq (hashTreeRoot desc value arena)
      (Ssz.hashTreeRootAt budget desc.erase value.erase) := by
  cases budget with
  | zero =>
      have positive := Desc.nesting_pos desc
      omega
  | succ budget =>
      rw [hashTreeRoot]
      apply rootStep_refines desc value arena budget safe descPhysical valuePhysical enough
      intro child member childDesc cursor childSafe childDescPhysical childPhysical childBudget
      exact hashTreeRootAt_refines childDesc child cursor budget childSafe childDescPhysical
        childPhysical childBudget
termination_by value.nesting
decreasing_by exact Value.child_nesting_lt _ _ (by assumption)

/-- Public pinned-root endpoint: only width safety and actual physical slices are
assumed. Capacities, optional limits and raw selectors are not logically capped. -/
theorem hashTreeRoot_refines (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (safe : SafeWidths desc) (descPhysical : desc.Physical) (valuePhysical : value.Physical) :
    Refines Eq (hashTreeRoot desc value arena) (Ssz.hashTreeRoot desc.erase value.erase) :=
  hashTreeRootAt_refines desc value arena desc.nesting safe descPhysical valuePhysical (Nat.le_refl _)

/-- Observable success cannot be excused by a host alternative. -/
theorem hashTreeRoot_success (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (safe : SafeWidths desc) (descPhysical : desc.Physical) (valuePhysical : value.Physical)
    (root : Ssz.Bytes) (success : (hashTreeRoot desc value arena).result = .ok root) :
    Ssz.hashTreeRoot desc.erase value.erase = .ok root := by
  have refined := hashTreeRoot_refines desc value arena safe descPhysical valuePhysical
  rw [Refines, success] at refined
  cases expected : Ssz.hashTreeRoot desc.erase value.erase with
  | error fault => rw [expected] at refined; cases refined
  | ok actual =>
      rw [expected] at refined
      cases refined with
      | ok _ _ same => exact congrArg Except.ok same.symm

/-- An unsafe raw declaration is rejected exactly as native scalar, not silently
identified with the different pinned raw behavior. -/
theorem hashTreeRoot_uint_oversized (width number : NatOperand) (arena : Delimited.ArenaState)
    (large : 32 < width.value) :
    hashTreeRoot (.primitive (.uint width)) (.uint number) arena =
      unchanged arena.used (.error (arithmeticError .badRepresentation)) := by
  have failed : layout (.primitive (.uint width)) (.uint number) arena =
      unchanged arena.used (.error (arithmeticError .badRepresentation)) := by
    simp only [layout, lift, scalar_uint_oversized width number large, bind, unchanged]
  have result := hashTreeRoot_layout_error (.primitive (.uint width)) (.uint number)
    arena (arithmeticError .badRepresentation) (by rw [failed]; rfl)
  simpa only [failed, unchanged] using result

/-- Exact success/semantic-error agreement, except the genuinely returned
resource exhaustion. No other native host error is an allowed alternative. -/
theorem hashTreeRoot_refinement_exact (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (safe : SafeWidths desc)
    (descPhysical : desc.Physical) (valuePhysical : value.Physical) :
    eraseResult (hashTreeRoot desc value arena).result =
        .ok (Ssz.hashTreeRoot desc.erase value.erase) ∨
      (hashTreeRoot desc value arena).result =
        .error (arithmeticError .scratchExhausted) :=
  ResultRefines.erase_or_exhausted _ _
    (hashTreeRoot_refines desc value arena safe descPhysical valuePhysical)

end SszNative.HashLayout

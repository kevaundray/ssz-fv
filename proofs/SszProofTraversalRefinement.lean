import SszProofTraversalWalkRefinement
import SszProofTraversalResources
import SszProofTraversalSafety
import SszProofTraversalWidths

set_option autoImplicit false

namespace SszNative.Proof

open Codec (Desc Value)

/-- Only a factored expression of the pinned post-layout walk, used to expose
its bind boundary; the executable traversal remains nodeStep/nodeAt. -/
def layoutNodeSpec (budget : Nat) (view : Ssz.MerkleLayout) (index fullDepth : Nat) :
    Except Ssz.Err Ssz.Bytes :=
  let contents := fun depth => match view.limit with
    | some capacity => Ssz.boundedNode budget view index depth 0 capacity
    | none => Ssz.progressiveNode budget view index depth 0 1
  match view.mixin with
  | none => contents fullDepth
  | some word =>
      let remaining := fullDepth - 1
      if Ssz.gindexBit index remaining then
        if remaining ≠ 0 then .error .pathIntoMixin else .ok word
      else contents remaining

theorem nodeRootAt_rebase_eq (budget : Nat) (desc : Ssz.Desc) (value : Ssz.Value)
    (index depth : Nat) :
    Ssz.nodeRootAt (budget + 1) desc value (Ssz.gindexRebase index depth) =
      (if depth = 0 then Ssz.hashTreeRoot desc value else
        Ssz.merkleLayout desc value >>= fun view => layoutNodeSpec budget view index depth) := by
  by_cases zero : depth = 0
  · simp [zero, Ssz.gindexRebase, Ssz.gindexBelow, Ssz.nodeRootAt]
  · have positive := rebase_positive index depth
    have measured := rebase_depth index depth
    have notRoot : Ssz.gindexRebase index depth ≠ 1 := by
      intro same
      rw [same, Nat.log2_one] at measured
      omega
    have length : Ssz.gindexLength (Ssz.gindexRebase index depth) = .ok depth := by
      simp [Ssz.gindexLength, Ssz.gindexDepth, show ¬Ssz.gindexRebase index depth < 1 by omega,
        measured, zero]
    simp only [Ssz.nodeRootAt, show ¬Ssz.gindexRebase index depth < 1 by omega,
      notRoot, beq_iff_eq, ↓reduceIte, length, zero]
    cases planned : Ssz.merkleLayout desc value with
    | error reason => rfl
    | ok view =>
        simp only [Except.bind, layoutNodeSpec]
        cases mixed : view.mixin with
        | none =>
            simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
            cases view.limit with
            | none => exact progressiveNode_rebase_congr budget view index depth depth 0 1 (Nat.le_refl _)
            | some capacity => exact boundedNode_rebase_congr budget view index depth depth 0 capacity (Nat.le_refl _)
        | some word =>
            simp only [Option.isSome_some, ↓reduceIte]
            rw [rebase_bit index depth (depth - 1) (by omega)]
            split
            · split <;> rfl
            · cases view.limit with
              | none => exact progressiveNode_rebase_congr budget view index depth (depth - 1) 0 1 (by omega)
              | some capacity => exact boundedNode_rebase_congr budget view index depth (depth - 1) 0 capacity (by omega)

private theorem bounded_capacity_eq (budget : Nat) (view : Ssz.MerkleLayout)
    (index depth base : Nat) (capacity : NatOperand) :
    Ssz.boundedNode budget view index depth base (2 ^ ceilDepth capacity) =
      Ssz.boundedNode budget view index depth base capacity.value := by
  rw [ceilDepth_eq_log2_nextPow2]
  simp only [Ssz.nextPow2, Nat.log2_two_pow, Ssz.boundedNode, Ssz.depthFor_pow]

private theorem nodeStep_refines (desc : Desc) (value : Value) (index : NatOperand)
    (depth budget : Nat) (arena : Delimited.ArenaState) (visit : ValueVisit value)
    (safe : HashLayout.SafeWidths desc) (descPhysical : desc.Physical)
    (valuePhysical : value.Physical) (indexPhysical : index.words.length < 2 ^ 64)
    (enough : desc.nesting ≤ budget + 1)
    (children : ∀ child (member : child ∈ value.children) childDesc childDepth cursor,
      HashLayout.SafeWidths childDesc → childDesc.Physical → child.Physical → childDesc.nesting ≤ budget →
      Refines Eq (visit child member childDesc childDepth cursor)
        (Ssz.nodeRootAt budget childDesc.erase child.erase (Ssz.gindexRebase index.value childDepth))) :
    Refines Eq (nodeStep desc value index depth arena visit)
      (Ssz.nodeRootAt (budget + 1) desc.erase value.erase (Ssz.gindexRebase index.value depth)) := by
  rw [nodeRootAt_rebase_eq]
  by_cases zero : depth = 0
  · simp only [nodeStep, zero, ↓reduceIte]
    exact liftLayout_refines Eq arena _ _
      (HashLayout.hashTreeRoot_refines desc value arena safe descPhysical valuePhysical)
  · simp only [zero, ↓reduceIte]
    have layoutRefined := liftLayout_refines HashLayout.LayoutRefines arena _ _
      (HashLayout.layout_refines desc value arena safe descPhysical valuePhysical)
    cases nativeEq : (HashLayout.layout desc value arena).result with
    | error reason =>
        have actual : (nodeStep desc value index depth arena visit).result = .error (.layout reason) := by
          simp only [nodeStep, zero, ↓reduceIte]
          split <;> simp_all
        change ResultRefines Eq _ _
        rw [actual]
        have lifted : (liftLayout arena (HashLayout.layout desc value arena)).result = .error (.layout reason) := by
          simp only [liftLayout, nativeEq, Except.mapError]
        rw [Refines, lifted] at layoutRefined
        cases layoutRefined with
        | exhausted reason allowed expected => exact .exhausted _ allowed _
        | error actual expected same => exact .error _ _ same
    | ok view =>
        obtain ⟨expected, layoutEq, related⟩ := HashLayout.layout_success desc value arena
          safe descPhysical valuePhysical view nativeEq
        let cursor := { arena with used := (HashLayout.layout desc value arena).used }
        let visitNode : NodeVisit view := fun position childDesc child selected childDepth childArena =>
          visit child (HashLayout.Layout.Generated.at_child desc value view
            (HashLayout.layout_generated desc value arena view nativeEq)
            position childDesc child selected) childDesc childDepth childArena
        have visits : ∀ position childDesc child selected childDepth childArena,
            Refines Eq (visitNode position childDesc child selected childDepth childArena)
              (Ssz.nodeRootAt budget childDesc.erase child.erase (Ssz.gindexRebase index.value childDepth)) := by
          intro position childDesc child selected childDepth childArena
          obtain ⟨childSafe, childDescPhysical, childPhysical, smaller⟩ :=
            HashLayout.layout_child_domain desc value view
              (HashLayout.layout_generated desc value arena view nativeEq)
              safe descPhysical valuePhysical position childDesc child selected
          exact children child _ childDesc childDepth childArena childSafe childDescPhysical childPhysical (by omega)
        have bounded : ∀ childDepth capacity,
            Refines Eq (boundedNode view index childDepth 0 (ceilDepth capacity) cursor visitNode)
              (Ssz.boundedNode budget expected index.value childDepth 0 capacity.value) := by
          intro childDepth capacity
          rw [← bounded_capacity_eq budget expected index.value childDepth 0 capacity]
          exact boundedNode_refines desc value arena cursor view expected index childDepth 0
            (ceilDepth capacity) budget visitNode safe descPhysical valuePhysical indexPhysical
            nativeEq layoutEq enough (by decide) visits
        have progressive : ∀ childDepth,
            Refines Eq (progressiveNode view index childDepth cursor visitNode)
              (Ssz.progressiveNode budget expected index.value childDepth 0 1) := by
          intro childDepth
          exact progressiveNode_refines desc value arena cursor view expected index childDepth budget
            visitNode safe descPhysical valuePhysical indexPhysical nativeEq layoutEq enough visits
        change ResultRefines Eq _ _
        simp only [nodeStep, zero, ↓reduceIte]
        split
        · simp_all
        · rename_i actual selected
          have same : actual = view := Except.ok.inj (selected.symm.trans nativeEq)
          subst actual
          simp only [layoutEq, Except.bind, layoutNodeSpec]
          rw [← related.2.2, ← related.2.1]
          cases mixed : view.mixin with
          | none =>
              simp only [Option.map]
              cases view.limit with
              | none => exact progressive depth
              | some capacity => exact bounded depth capacity
          | some word =>
              simp only [Indices.bit_refines index (depth - 1) indexPhysical]
              split
              · split
                · exact .error _ _ rfl
                · exact .ok _ _ rfl
              · simp only [Option.map]
                cases view.limit with
                | none => exact progressive (depth - 1)
                | some capacity => exact bounded (depth - 1) capacity

/-- The child obligations are discharged by actual finite-value recursion, not
by assuming success, readability, enough scratch, or future execution. -/
theorem nodeAt_refines (desc : Desc) (value : Value) (index : NatOperand)
    (depth budget : Nat) (arena : Delimited.ArenaState)
    (safe : HashLayout.SafeWidths desc) (descPhysical : desc.Physical)
    (valuePhysical : value.Physical) (indexPhysical : index.words.length < 2 ^ 64)
    (enough : desc.nesting ≤ budget) :
    Refines Eq (nodeAt desc value index depth arena)
      (Ssz.nodeRootAt budget desc.erase value.erase (Ssz.gindexRebase index.value depth)) := by
  cases budget with
  | zero => have positive := Desc.nesting_pos desc; omega
  | succ budget =>
      rw [nodeAt]
      apply nodeStep_refines desc value index depth budget arena _ safe descPhysical valuePhysical indexPhysical enough
      intro child member childDesc childDepth childArena childSafe childDescPhysical childPhysical childEnough
      exact nodeAt_refines childDesc child index childDepth budget childArena
        childSafe childDescPhysical childPhysical indexPhysical childEnough
termination_by value.nesting
decreasing_by exact Value.child_nesting_lt _ _ (by assumption)

/-- Public pinned node reading on the established raw hash domain. Arbitrarily
large logical capacities and indices remain legal; only physical slices are
bounded. The only permitted divergence is actual scratch exhaustion. -/
theorem nodeRoot_refines (desc : Desc) (value : Value) (index : NatOperand)
    (arena : Delimited.ArenaState) (safe : HashLayout.SafeWidths desc)
    (descPhysical : desc.Physical) (valuePhysical : value.Physical)
    (indexPhysical : index.words.length < 2 ^ 64) :
    Refines Eq (nodeRoot desc value index arena) (Ssz.nodeRoot desc.erase value.erase index.value) := by
  by_cases zero : index.value = 0
  · rw [nodeRoot_zero desc value index arena zero]
    have positive := Desc.nesting_pos desc
    unfold Ssz.nodeRoot
    cases nesting : desc.erase.nesting with
    | zero =>
        have same := Desc.erase_nesting desc
        omega
    | succ nesting =>
        simp only [zero, Nat.add_zero, Ssz.nodeRootAt, Nat.zero_lt_one, ↓reduceIte]
        exact .error _ _ rfl
  · have nonzero : index.wordCount ≠ 0 := fun count => zero ((Indices.wordCount_zero_iff index).mp count)
    simp only [nodeRoot, nonzero, ↓reduceIte]
    have refined := nodeAt_refines desc value index (Indices.depth index)
      (desc.erase.nesting + index.value) arena safe descPhysical valuePhysical indexPhysical
      (by rw [Desc.erase_nesting]; omega)
    rw [Indices.depth_value, rebase_self index.value (by omega)] at refined
    exact refined

private theorem eraseError_map {α β : Type} (reason : Error) (f : α → β) :
    eraseResult (.error reason : Except Error β) =
      (eraseResult (.error reason : Except Error α)).map (fun inner => inner.map f) := by
  cases reason with
  | indices reason => exact Indices.eraseResult_map (.error reason) f
  | layout reason => exact HashLayout.eraseResult_map (.error reason) f
  | _ => rfl

theorem nodeRoot_refinement_exact (desc : Desc) (value : Value) (index : NatOperand)
    (arena : Delimited.ArenaState) (safe : HashLayout.SafeWidths desc)
    (descPhysical : desc.Physical) (valuePhysical : value.Physical)
    (indexPhysical : index.words.length < 2 ^ 64) :
    eraseResult (nodeRoot desc value index arena).result =
        .ok (Ssz.nodeRoot desc.erase value.erase index.value) ∨
      ∃ reason, (nodeRoot desc value index arena).result = .error reason ∧ IsExhausted reason := by
  have refined := nodeRoot_refines desc value index arena safe descPhysical valuePhysical indexPhysical
  cases refined with
  | exhausted reason allowed expected => exact Or.inr ⟨reason, rfl, allowed⟩
  | ok actual expected same => cases same; exact Or.inl rfl
  | error actual expected same =>
      apply Or.inl
      have mapped := congrArg
        (fun result : Except Serialize.Host (Except Ssz.Err Unit) =>
          result.map (fun inner => inner.map (fun _ => (#[] : Ssz.Bytes)))) same
      rw [← eraseError_map] at mapped
      exact mapped

/-- Checked-ready endpoint: exact pinned semantics or the actually returned
scratch error, together with the recursively derived retained trace, monotone
valid cursor, and unconditional successful native hash width. -/
theorem nodeRoot_checked_ready (desc : Desc) (value : Value) (index : NatOperand)
    (arena : Delimited.ArenaState) (safe : HashLayout.SafeWidths desc)
    (descPhysical : desc.Physical) (valuePhysical : value.Physical)
    (indexPhysical : index.words.length < 2 ^ 64) :
    (eraseResult (nodeRoot desc value index arena).result =
        .ok (Ssz.nodeRoot desc.erase value.erase index.value) ∨
      ∃ reason, (nodeRoot desc value index arena).result = .error reason ∧ IsExhausted reason) ∧
    TraversalTrace arena (nodeRoot desc value index arena).effects (nodeRoot desc value index arena).used ∧
    HashLayout.CursorSafe arena (nodeRoot desc value index arena).used ∧
    (∀ root, (nodeRoot desc value index arena).result = .ok root → root.size = 32) :=
  ⟨nodeRoot_refinement_exact desc value index arena safe descPhysical valuePhysical indexPhysical,
    nodeRoot_trace desc value index arena, nodeRoot_cursorSafe desc value index arena,
    nodeRoot_size_raw desc value index arena⟩

end SszNative.Proof

import SszProofTraversal

set_option autoImplicit false

namespace SszNative.Proof

open Codec (Desc Value)

theorem boundedNode_trace (view : HashLayout.Layout) (index : NatOperand)
    (depth base treeDepth : Nat) (arena : Delimited.ArenaState) (visit : NodeVisit view)
    (visits : ∀ position desc value selected depth cursor,
      TraversalTrace cursor (visit position desc value selected depth cursor).effects
        (visit position desc value selected depth cursor).used) :
    TraversalTrace arena (boundedNode view index depth base treeDepth arena visit).effects
      (boundedNode view index depth base treeDepth arena visit).used := by
  unfold boundedNode
  split
  · dsimp only
    split
    · exact unchanged_traversalTrace _ _
    · split
      · exact rangeRoot_trace _ _ _ _ _
      · exact unchanged_traversalTrace _ _
  · split
    · exact unchanged_traversalTrace _ _
    · dsimp only
      split
      · exact unchanged_traversalTrace _ _
      · split
        · exact unchanged_traversalTrace _ _
        · exact visits _ _ _ _ _ _

theorem progressiveFrom_trace (view : HashLayout.Layout) (start capacity : Nat)
    (positive : 0 < capacity) (arena : Delimited.ArenaState) :
    TraversalTrace arena (progressiveFrom view start capacity positive arena).effects
      (progressiveFrom view start capacity positive arena).used := by
  rw [progressiveFrom]
  split
  · rename_i nonempty
    apply bind_traversalTrace
    · exact rangeRoot_trace _ _ _ _ _
    · intro left used
      split
      · exact unchanged_traversalTrace _ _
      · apply bind_traversalTrace
        · exact progressiveFrom_trace _ _ _ _ _
        · intro right used'
          exact unchanged_traversalTrace _ _
  · exact unchanged_traversalTrace _ _
termination_by view.count - start
decreasing_by
  have step := progressiveTake_positive (view.count - start) capacity (by omega) positive
  omega

theorem progressiveNodeFrom_trace (view : HashLayout.Layout) (index : NatOperand)
    (visit : NodeVisit view)
    (visits : ∀ position desc value selected depth cursor,
      TraversalTrace cursor (visit position desc value selected depth cursor).effects
        (visit position desc value selected depth cursor).used)
    (depth start capacity : Nat) (positive : 0 < capacity) (arena : Delimited.ArenaState) :
    TraversalTrace arena
      (progressiveNodeFrom view index visit depth start capacity positive arena).effects
      (progressiveNodeFrom view index visit depth start capacity positive arena).used := by
  induction depth generalizing start capacity arena with
  | zero =>
      simp only [progressiveNodeFrom]
      split
      · exact progressiveFrom_trace _ _ _ _ _
      · exact unchanged_traversalTrace _ _
  | succ depth ih =>
      simp only [progressiveNodeFrom]
      split
      · exact unchanged_traversalTrace _ _
      · split
        · exact boundedNode_trace _ _ _ _ _ _ _ visits
        · exact ih _ _ _ _

theorem progressiveNode_trace (view : HashLayout.Layout) (index : NatOperand)
    (depth : Nat) (arena : Delimited.ArenaState) (visit : NodeVisit view)
    (visits : ∀ position desc value selected depth cursor,
      TraversalTrace cursor (visit position desc value selected depth cursor).effects
        (visit position desc value selected depth cursor).used) :
    TraversalTrace arena (progressiveNode view index depth arena visit).effects
      (progressiveNode view index depth arena visit).used :=
  progressiveNodeFrom_trace view index visit visits depth 0 1 (by decide) arena

theorem nodeStep_trace (desc : Desc) (value : Value) (index : NatOperand) (fullDepth : Nat)
    (arena : Delimited.ArenaState) (visit : ValueVisit value)
    (visits : ∀ child member childDesc depth cursor,
      TraversalTrace cursor (visit child member childDesc depth cursor).effects
        (visit child member childDesc depth cursor).used) :
    TraversalTrace arena (nodeStep desc value index fullDepth arena visit).effects
      (nodeStep desc value index fullDepth arena visit).used := by
  simp only [nodeStep]
  split
  · exact liftLayout_traversalTrace arena _ (HashLayout.hashTreeRoot_trace desc value arena)
  · split
    · exact liftLayout_traversalTrace arena _ (HashLayout.layout_trace desc value arena)
    · apply TraversalTrace.append
      · exact liftLayout_traversalTrace arena _ (HashLayout.layout_trace desc value arena)
      · dsimp only
        split
        · split
          · apply boundedNode_trace
            intro position childDesc child selected depth cursor
            exact visits _ _ _ _ _
          · apply progressiveNode_trace
            intro position childDesc child selected depth cursor
            exact visits _ _ _ _ _
        · split
          · split
            · exact unchanged_traversalTrace _ _
            · exact unchanged_traversalTrace _ _
          · split
            · apply boundedNode_trace
              intro position childDesc child selected depth cursor
              exact visits _ _ _ _ _
            · apply progressiveNode_trace
              intro position childDesc child selected depth cursor
              exact visits _ _ _ _ _

/-- The entire source recursion has an actual ordered trace. No arena-capacity,
future child execution, successful-path, or readable-claim premise is needed. -/
theorem nodeAt_trace (desc : Desc) (value : Value) (index : NatOperand) (depth : Nat)
    (arena : Delimited.ArenaState) :
    TraversalTrace arena (nodeAt desc value index depth arena).effects
      (nodeAt desc value index depth arena).used := by
  rw [nodeAt]
  apply nodeStep_trace
  intro child member childDesc childDepth childArena
  exact nodeAt_trace childDesc child index childDepth childArena
termination_by value.nesting
decreasing_by exact Value.child_nesting_lt _ _ (by assumption)

theorem nodeRoot_trace (desc : Desc) (value : Value) (index : NatOperand)
    (arena : Delimited.ArenaState) :
    TraversalTrace arena (nodeRoot desc value index arena).effects
      (nodeRoot desc value index arena).used := by
  unfold nodeRoot
  split
  · exact unchanged_traversalTrace arena _
  · exact nodeAt_trace _ _ _ _ _

theorem nodeRoot_cursorSafe (desc : Desc) (value : Value) (index : NatOperand)
    (arena : Delimited.ArenaState) :
    HashLayout.CursorSafe arena (nodeRoot desc value index arena).used :=
  (nodeRoot_trace desc value index arena).cursorSafe

theorem nodeRoot_used_mono (desc : Desc) (value : Value) (index : NatOperand)
    (arena : Delimited.ArenaState) : arena.used ≤ (nodeRoot desc value index arena).used :=
  (nodeRoot_cursorSafe desc value index arena).1

theorem nodeRoot_valid (desc : Desc) (value : Value) (index : NatOperand)
    (arena : Delimited.ArenaState) (valid : Arena.Valid arena.base arena.capacity arena.used) :
    Arena.Valid arena.base arena.capacity (nodeRoot desc value index arena).used :=
  (nodeRoot_cursorSafe desc value index arena).2 valid

/-- No proof output reservation or initialized output slot is hidden inside a
node read; its complete resource trace consists solely of actual layout calls. -/
theorem TraversalTrace.layout_events {arena : Delimited.ArenaState}
    {effects : List Effect} {used : Nat} (trace : TraversalTrace arena effects used) :
    ∀ effect ∈ effects, ∃ cursor outcome, effect = Effect.layout cursor outcome := by
  induction trace with
  | nil arena => simp
  | layout arena outcome ran rest used later ih =>
      intro effect member
      rcases List.mem_cons.mp member with same | member
      · exact ⟨arena, outcome, same⟩
      · exact ih effect member

end SszNative.Proof

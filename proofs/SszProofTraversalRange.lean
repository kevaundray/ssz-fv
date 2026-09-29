import SszProofTypes
import SszHashLayoutResources

set_option autoImplicit false

namespace SszNative.Proof

/-- The range loop roots one borrowed leaf, then performs the native checked
accumulator push. Neither later leaves nor padding are materialized. -/
def rangeLoop (view : HashLayout.Layout) (depth : Nat) :
    (remaining start : Nat) → MerkleAccumulator.Accumulator Ssz.Bytes →
      Delimited.ArenaState → Outcome Ssz.Bytes
  | 0, _, tree, arena => unchanged arena.used
      ((MerkleAccumulator.finishDepth rawCombine Ssz.zeroChunk tree depth).mapError
        (fun reason => Error.layout (.merkle reason)))
  | remaining + 1, start, tree, arena =>
      bind (liftLayout arena (HashLayout.indexedRoot view start arena)) fun root used =>
        let pushed := MerkleAccumulator.push rawCombine Ssz.zeroChunk tree root
        bind (unchanged used (pushed.2.mapError (fun reason => Error.layout (.merkle reason))))
          fun _ used => rangeLoop view depth remaining (start + 1) pushed.1
            { arena with used := used }

def rangeRoot (view : HashLayout.Layout) (start stop depth : Nat)
    (arena : Delimited.ArenaState) : Outcome Ssz.Bytes :=
  rangeLoop view depth (stop - start) start (MerkleAccumulator.new Ssz.zeroChunk) arena

/-- Traversal allocates only through the borrowed-layout subsystem. Every event
contains its actual child outcome, including failed arithmetic and abandoned
scratch. A cursor is threaded between events rather than inferred from totals. -/
inductive TraversalTrace : Delimited.ArenaState → List Effect → Nat → Prop where
  | nil (arena : Delimited.ArenaState) : TraversalTrace arena [] arena.used
  | layout (arena : Delimited.ArenaState) (outcome : HashLayout.Outcome Unit)
      (ran : HashLayout.Trace arena outcome.effects outcome.used)
      (rest : List Effect) (used : Nat)
      (later : TraversalTrace { arena with used := outcome.used } rest used) :
      TraversalTrace arena (.layout arena outcome :: rest) used

theorem TraversalTrace.append (arena : Delimited.ArenaState) (first second : List Effect)
    (middle used : Nat) (before : TraversalTrace arena first middle)
    (after : TraversalTrace { arena with used := middle } second used) :
    TraversalTrace arena (first ++ second) used := by
  induction before with
  | nil arena => exact after
  | layout arena outcome ran rest middle later ih =>
      exact .layout arena outcome ran (rest ++ second) used (ih after)

theorem TraversalTrace.cursorSafe {arena : Delimited.ArenaState} {effects : List Effect}
    {used : Nat} (trace : TraversalTrace arena effects used) :
    HashLayout.CursorSafe arena used := by
  induction trace with
  | nil arena => exact HashLayout.cursorSafe_refl arena
  | layout arena outcome ran rest used later ih =>
      exact HashLayout.cursorSafe_trans arena outcome.used used ran.cursorSafe ih

theorem unchanged_traversalTrace {α : Type} (arena : Delimited.ArenaState)
    (result : Except Error α) :
    TraversalTrace arena (unchanged arena.used result).effects (unchanged arena.used result).used :=
  .nil arena

theorem liftLayout_traversalTrace {α : Type} (arena : Delimited.ArenaState)
    (outcome : HashLayout.Outcome α)
    (ran : HashLayout.Trace arena outcome.effects outcome.used) :
    TraversalTrace arena (liftLayout arena outcome).effects (liftLayout arena outcome).used :=
  .layout arena _ ran [] outcome.used (.nil { arena with used := outcome.used })

theorem bind_traversalTrace {α β : Type} (arena : Delimited.ArenaState)
    (first : Outcome α) (next : α → Nat → Outcome β)
    (before : TraversalTrace arena first.effects first.used)
    (after : ∀ value used, TraversalTrace { arena with used := used }
      (next value used).effects (next value used).used) :
    TraversalTrace arena (bind first next).effects (bind first next).used := by
  cases result : first.result with
  | error reason => simpa only [bind, result] using before
  | ok value =>
      simpa only [bind, result] using
        TraversalTrace.append arena first.effects (next value first.used).effects
          first.used (next value first.used).used before (after value first.used)

theorem rangeLoop_trace (view : HashLayout.Layout) (depth remaining start : Nat)
    (tree : MerkleAccumulator.Accumulator Ssz.Bytes) (arena : Delimited.ArenaState) :
    TraversalTrace arena (rangeLoop view depth remaining start tree arena).effects
      (rangeLoop view depth remaining start tree arena).used := by
  induction remaining generalizing start tree arena with
  | zero => exact unchanged_traversalTrace arena _
  | succ remaining ih =>
      simp only [rangeLoop]
      apply bind_traversalTrace
      · exact liftLayout_traversalTrace arena _ (HashLayout.indexedRoot_trace view start arena)
      · intro root used
        apply bind_traversalTrace
        · exact unchanged_traversalTrace { arena with used := used } _
        · intro pushed used'
          exact ih (start + 1) _ { arena with used := used' }

theorem rangeRoot_trace (view : HashLayout.Layout) (start stop depth : Nat)
    (arena : Delimited.ArenaState) :
    TraversalTrace arena (rangeRoot view start stop depth arena).effects
      (rangeRoot view start stop depth arena).used :=
  rangeLoop_trace view depth (stop - start) start _ arena

theorem rangeRoot_cursorSafe (view : HashLayout.Layout) (start stop depth : Nat)
    (arena : Delimited.ArenaState) : HashLayout.CursorSafe arena (rangeRoot view start stop depth arena).used :=
  (rangeRoot_trace view start stop depth arena).cursorSafe

theorem rangeRoot_empty (view : HashLayout.Layout) (start depth : Nat)
    (arena : Delimited.ArenaState) :
    rangeRoot view start start depth arena = unchanged arena.used
      ((MerkleAccumulator.finishDepth rawCombine Ssz.zeroChunk
        (MerkleAccumulator.new Ssz.zeroChunk) depth).mapError
          (fun reason => Error.layout (.merkle reason))) := by
  simp only [rangeRoot, Nat.sub_self, rangeLoop]

end SszNative.Proof

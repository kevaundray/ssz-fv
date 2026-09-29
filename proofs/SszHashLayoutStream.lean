import SszHashLayoutTypes

set_option autoImplicit false

namespace SszNative.HashLayout

/-- These are the accepted native finite states, not an accumulated leaf array. -/
inductive TreeState where
  | bounded (limit : NatOperand) (state : MerkleAccumulator.Accumulator Ssz.Bytes)
  | progressive (state : MerkleProgressive.Accumulator Ssz.Bytes)

def TreeState.new : Option NatOperand → TreeState
  | some limit => .bounded limit (MerkleAccumulator.new Ssz.zeroChunk)
  | none => .progressive (MerkleProgressive.new Ssz.zeroChunk)

def TreeState.limit : TreeState → Option NatOperand
  | .bounded limit _ => some limit
  | .progressive _ => none

def TreeState.count : TreeState → Nat
  | .bounded _ state => state.count
  | .progressive state => state.count

def TreeState.push (tree : TreeState) (node : Ssz.Bytes) : Except Error TreeState :=
  match tree with
  | .bounded limit state =>
      let pushed := MerkleAccumulator.push Ssz.combine Ssz.zeroChunk state node
      (pushed.2.map (fun _ => .bounded limit pushed.1)).mapError Error.merkle
  | .progressive state =>
      let pushed := MerkleProgressive.push Ssz.combine Ssz.zeroChunk state node
      (pushed.2.map (fun _ => .progressive pushed.1)).mapError Error.merkle

def TreeState.finish : TreeState → Except Error Ssz.Bytes
  | .bounded limit state =>
      (MerkleAccumulator.finish Ssz.combine Ssz.zeroChunk state (some limit)).mapError Error.merkle
  | .progressive state => .ok (MerkleProgressive.finish Ssz.combine Ssz.zeroChunk state)

/-- A generated-state invariant uses mathematical leaves only in its proposition. -/
def TreeState.Invariant (chunks : Array Ssz.Bytes) : TreeState → Prop
  | .bounded _ state => MerkleAccumulator.Occupied Ssz.combine Ssz.zeroChunk chunks state
  | .progressive state => MerkleProgressive.Invariant Ssz.combine Ssz.zeroChunk chunks.toList state

theorem TreeState.new_invariant (limit : Option NatOperand) :
    (TreeState.new limit).Invariant #[] := by
  cases limit with
  | none => exact MerkleProgressive.new_invariant Ssz.combine Ssz.zeroChunk
  | some limit => exact MerkleAccumulator.new_occupied Ssz.combine Ssz.zeroChunk

theorem TreeState.invariant_count (chunks : Array Ssz.Bytes) (tree : TreeState)
    (valid : tree.Invariant chunks) : tree.count = chunks.size := by
  cases tree with
  | bounded limit state => exact valid.1
  | progressive state =>
      change state.count = chunks.size
      simpa using valid.2.1

theorem TreeState.push_invariant (chunks : Array Ssz.Bytes) (tree : TreeState)
    (node : Ssz.Bytes) (valid : tree.Invariant chunks)
    (room : chunks.size < MerkleAccumulator.maxCount) :
    ∃ next, tree.push node = .ok next ∧ next.Invariant (chunks.push node) ∧
      next.limit = tree.limit := by
  have room' : tree.count < MerkleAccumulator.maxCount := by
    rw [TreeState.invariant_count chunks tree valid]
    exact room
  cases tree with
  | bounded limit state =>
      refine ⟨.bounded limit (MerkleAccumulator.pushNode Ssz.combine Ssz.zeroChunk state node), ?_, ?_, rfl⟩
      · simp only [TreeState.push, MerkleAccumulator.push_room Ssz.combine Ssz.zeroChunk state node room',
          Except.map, Except.mapError]
      · exact MerkleAccumulator.pushNode_occupied Ssz.combine Ssz.zeroChunk chunks state node valid room'
  | progressive state =>
      refine ⟨.progressive (MerkleProgressive.pushNode Ssz.combine Ssz.zeroChunk state node), ?_, ?_, rfl⟩
      · simp only [TreeState.push, MerkleProgressive.push_room Ssz.combine Ssz.zeroChunk state node room',
          Except.map, Except.mapError]
      · change MerkleProgressive.Invariant Ssz.combine Ssz.zeroChunk
          (chunks.push node).toList (MerkleProgressive.pushNode Ssz.combine Ssz.zeroChunk state node)
        simpa only [Array.toList_push] using MerkleProgressive.pushNode_invariant
          Ssz.combine Ssz.zeroChunk chunks.toList state node valid room'

/-- Finish checks the bounded capacity only after the supplied state has been
built. The progressive branch closes the actual current tree and completed spine. -/
def mathematicalRoot (chunks : Array Ssz.Bytes) (limit : Option NatOperand) :
    Except Ssz.Err Ssz.Bytes :=
  match limit with
  | some capacity => Ssz.merkleizeBounded chunks (some capacity.value)
  | none => .ok (Ssz.merkleizeProgressive chunks.toList)

theorem TreeState.finish_refines (chunks : Array Ssz.Bytes) (tree : TreeState)
    (valid : tree.Invariant chunks) :
    eraseResult tree.finish = .ok (mathematicalRoot chunks tree.limit) := by
  cases tree with
  | bounded limit state =>
      have refined := MerkleAccumulator.finish_refines chunks state (some limit) valid
      cases resultEq : MerkleAccumulator.finish Ssz.combine Ssz.zeroChunk state (some limit) with
      | ok root =>
          simp only [resultEq, MerkleAccumulator.eraseResult, Option.map, Except.ok.injEq] at refined
          simp only [TreeState.finish, resultEq, Except.mapError, eraseResult,
            TreeState.limit, mathematicalRoot]
          exact congrArg Except.ok refined
      | error reason =>
          cases reason with
          | merkleizeLimit count capacity =>
              simp only [resultEq, MerkleAccumulator.eraseResult, Option.map, Except.ok.injEq] at refined
              simp only [TreeState.finish, resultEq, Except.mapError, eraseResult,
                TreeState.limit, mathematicalRoot]
              exact congrArg Except.ok refined
          | outputTooSmall =>
              simp only [resultEq, MerkleAccumulator.eraseResult] at refined
              cases refined
  | progressive state =>
      change Except.ok (Except.ok (MerkleProgressive.finish Ssz.combine Ssz.zeroChunk state)) = _
      rw [MerkleProgressive.finish_refines chunks.toList state valid]
      rfl

/-- A leaf completes, with its resource effects, before the next push is attempted.
The sole recursion counter is the physical number of remaining indexed leaves. -/
def stream (leaf : Nat → Delimited.ArenaState → Outcome Ssz.Bytes) :
    Nat → Nat → TreeState → Delimited.ArenaState → Outcome Ssz.Bytes
  | 0, _, tree, arena => unchanged arena.used tree.finish
  | remaining + 1, index, tree, arena =>
      bind (leaf index arena) fun node used =>
        bind (lift used (tree.push node)) fun next used =>
          stream leaf remaining (index + 1) next { arena with used := used }

/-- A child rejection has priority over both accumulator overflow and final
capacity rejection, and retains exactly that child's committed cursor and trace. -/
theorem stream_child_error (leaf : Nat → Delimited.ArenaState → Outcome Ssz.Bytes)
    (remaining index : Nat) (tree : TreeState) (arena : Delimited.ArenaState)
    (reason : Error) (failed : (leaf index arena).result = .error reason) :
    stream leaf (remaining + 1) index tree arena =
      ⟨.error reason, (leaf index arena).used, (leaf index arena).effects⟩ := by
  simp only [stream, bind, failed]

/-- No capacity or mix-in operation can precede the final leaf. -/
theorem stream_done (leaf : Nat → Delimited.ArenaState → Outcome Ssz.Bytes)
    (index : Nat) (tree : TreeState) (arena : Delimited.ArenaState) :
    stream leaf 0 index tree arena = unchanged arena.used tree.finish := rfl

end SszNative.HashLayout

import SszHashLayoutRoot
import SszHashLayoutPackedProofs
import Ssz.Proofs.Hash.Sha256Laws

set_option autoImplicit false

namespace SszNative.HashLayout

private theorem combine_size (left right : Ssz.Bytes) :
    (Ssz.combine left right).size = 32 :=
  Ssz.Sha256.hash_size (ByteArray.mk (left ++ right))

private theorem zeroChunk_size : Ssz.zeroChunk.size = 32 := by
  simp only [Ssz.zeroChunk, Array.size_replicate, Ssz.bytesPerChunk]

private theorem carry_size (state : MerkleAccumulator.Accumulator Ssz.Bytes)
    (node : Ssz.Bytes) (height : Nat) (complete : node.size = 32) :
    (MerkleAccumulator.carry Ssz.combine Ssz.zeroChunk state node height).size = 32 := by
  cases height with
  | zero => exact complete
  | succ height => exact combine_size _ _

private theorem advanceZero_size (depth : Nat) (node : Ssz.Bytes) (complete : node.size = 32) :
    (MerkleAccumulator.advanceZero Ssz.combine depth node).size = 32 := by
  induction depth generalizing node with
  | zero => exact complete
  | succ depth ih => exact ih _ (combine_size _ _)

private theorem rootFold_size (state : MerkleAccumulator.Accumulator Ssz.Bytes)
    (remaining height count : Nat) (node : Ssz.Bytes)
    (cursor : MerkleAccumulator.ZeroCursor Ssz.Bytes) (complete : node.size = 32) :
    (MerkleAccumulator.rootFold Ssz.combine Ssz.zeroChunk state remaining height count node cursor).size = 32 := by
  induction count generalizing height node cursor with
  | zero => exact complete
  | succ count ih =>
      unfold MerkleAccumulator.rootFold
      split <;> apply ih <;> exact combine_size _ _

private theorem rootAtDepth_size (state : MerkleAccumulator.Accumulator Ssz.Bytes)
    (depth : Nat) (complete : ∀ index, (state.nodes index).size = 32) :
    (MerkleAccumulator.rootAtDepth Ssz.combine Ssz.zeroChunk state depth).size = 32 := by
  unfold MerkleAccumulator.rootAtDepth
  split
  · exact advanceZero_size depth Ssz.zeroChunk zeroChunk_size
  · apply rootFold_size
    unfold MerkleAccumulator.slot
    split
    · exact complete _
    · exact zeroChunk_size

private theorem foldCompleted_size (nodes : Fin 32 → Ssz.Bytes) (level : Nat)
    (node : Ssz.Bytes) (complete : node.size = 32) :
    (MerkleProgressive.foldCompleted Ssz.combine Ssz.zeroChunk nodes level node).size = 32 := by
  induction level generalizing node with
  | zero => exact complete
  | succ level ih => exact ih _ (combine_size _ _)

/-- All bounded state cells start complete and retain complete roots after each
push. Progressive finishing hashes every occupied chunk even at depth zero. -/
def TreeState.Complete : TreeState → Prop
  | .bounded _ state => ∀ index, (state.nodes index).size = 32
  | .progressive _ => True

theorem TreeState.new_complete (limit : Option NatOperand) : (TreeState.new limit).Complete := by
  cases limit with
  | none => trivial
  | some limit => exact fun _ => zeroChunk_size

theorem TreeState.push_complete (tree next : TreeState) (node : Ssz.Bytes)
    (complete : tree.Complete) (nodeComplete : node.size = 32)
    (pushed : tree.push node = .ok next) : next.Complete := by
  cases tree with
  | bounded limit state =>
      simp only [TreeState.push, MerkleAccumulator.push] at pushed
      split at pushed
      · cases pushed
      · cases pushed
        intro index
        simp only [MerkleAccumulator.pushNode]
        split
        · exact carry_size state node _ nodeComplete
        · exact complete index
  | progressive state =>
      simp only [TreeState.push, MerkleProgressive.push] at pushed
      split at pushed
      · cases pushed
      · cases pushed
        trivial

theorem TreeState.finish_size (tree : TreeState) (root : Ssz.Bytes)
    (complete : tree.Complete) (success : tree.finish = .ok root) : root.size = 32 := by
  cases tree with
  | bounded limit state =>
      simp only [TreeState.finish, MerkleAccumulator.finish] at success
      cases depthEq : MerkleAccumulator.boundedDepth state.count (some limit) with
      | error reason => simp only [depthEq, Except.mapError] at success; cases success
      | ok depth =>
          simp only [depthEq, Except.mapError] at success
          have same : MerkleAccumulator.rootAtDepth Ssz.combine Ssz.zeroChunk state depth = root :=
            Except.ok.inj success
          rw [← same]
          exact rootAtDepth_size state depth complete
  | progressive state =>
      cases success
      apply foldCompleted_size
      split
      · exact zeroChunk_size
      · exact combine_size _ _

 theorem leafRoot_size (view : Layout) (index : Nat) (arena : Delimited.ArenaState)
    (visit : (desc : Codec.Desc) → (value : Codec.Value) →
      view.nested index = some (desc, value) → Delimited.ArenaState → Outcome Ssz.Bytes)
    (children : ∀ desc value selected cursor root,
      (visit desc value selected cursor).result = .ok root → root.size = 32)
    (root : Ssz.Bytes) (success : (leafRoot view index arena visit).result = .ok root) :
    root.size = 32 := by
  unfold leafRoot at success
  split at success
  · split at success
    · exact packedChunk_size _ _ root success
    · split at success
      · cases success; exact zeroChunk_size
      · exact children _ _ _ _ root success
  · cases success; exact zeroChunk_size

 theorem stream_size (leaf : Nat → Delimited.ArenaState → Outcome Ssz.Bytes)
    (remaining index : Nat) (tree : TreeState) (arena : Delimited.ArenaState)
    (complete : tree.Complete)
    (each : ∀ i cursor root, (leaf i cursor).result = .ok root → root.size = 32)
    (root : Ssz.Bytes) (success : (stream leaf remaining index tree arena).result = .ok root) :
    root.size = 32 := by
  induction remaining generalizing index tree arena with
  | zero => exact TreeState.finish_size tree root complete success
  | succ remaining ih =>
      simp only [stream, bind] at success
      cases childEq : (leaf index arena).result with
      | error reason => simp only [childEq] at success; cases success
      | ok node =>
          simp only [childEq, lift, unchanged] at success
          cases pushed : tree.push node with
          | error reason => simp only [pushed] at success; cases success
          | ok next =>
              simp only [pushed] at success
              exact ih (index + 1) next _
                (TreeState.push_complete tree next node complete (each index arena node childEq) pushed)
                success

 theorem mixRoot_size (mixin : Option Ssz.Bytes) (root : Ssz.Bytes) (complete : root.size = 32) :
    (mixRoot mixin root).size = 32 := by
  cases mixin with
  | none => exact complete
  | some word => exact combine_size _ _

/-- No domain predicate is needed for the width of an actual successful native
root. This proof follows finite-state execution, independently of pinned rooting. -/
theorem hashTreeRoot_size_raw (desc : Codec.Desc) (value : Codec.Value)
    (arena : Delimited.ArenaState) (root : Ssz.Bytes)
    (success : (hashTreeRoot desc value arena).result = .ok root) : root.size = 32 := by
  rw [hashTreeRoot] at success
  simp only [rootStep] at success
  split at success
  · cases success
  · rename_i view laidOut
    simp only [bind] at success
    split at success
    · cases success
    · rename_i node rooted
      cases success
      apply mixRoot_size
      apply stream_size _ _ _ _ _ (TreeState.new_complete view.limit) _ node rooted
      intro index cursor childRoot childSuccess
      apply leafRoot_size _ _ _ _ _ childRoot childSuccess
      intro childDesc child selected childArena result childResult
      have member := Layout.Generated.at_child desc value view
        (layout_generated desc value arena view laidOut) index childDesc child selected
      exact hashTreeRoot_size_raw childDesc child childArena result childResult
termination_by value.nesting
decreasing_by exact Codec.Value.child_nesting_lt _ _ (by assumption)

end SszNative.HashLayout

import SszProofTraversal
import SszHashLayoutWidths

set_option autoImplicit false

namespace SszNative.Proof

private theorem zero_size : Ssz.zeroChunk.size = 32 := by
  simp [Ssz.zeroChunk, Ssz.bytesPerChunk]

private theorem advanceZero_size (depth : Nat) (node : Ssz.Bytes) (complete : node.size = 32) :
    (MerkleAccumulator.advanceZero rawCombine depth node).size = 32 := by
  induction depth generalizing node with
  | zero => exact complete
  | succ depth ih => exact ih _ (rawCombine_size _ _)

private theorem carry_size (tree : MerkleAccumulator.Accumulator Ssz.Bytes)
    (node : Ssz.Bytes) (height : Nat) (complete : node.size = 32) :
    (MerkleAccumulator.carry rawCombine Ssz.zeroChunk tree node height).size = 32 := by
  cases height with
  | zero => exact complete
  | succ height => exact rawCombine_size _ _

private theorem rootFold_size (tree : MerkleAccumulator.Accumulator Ssz.Bytes)
    (remaining height count : Nat) (node : Ssz.Bytes) (cursor : MerkleAccumulator.ZeroCursor Ssz.Bytes)
    (complete : node.size = 32) :
    (MerkleAccumulator.rootFold rawCombine Ssz.zeroChunk tree remaining height count node cursor).size = 32 := by
  induction count generalizing height node cursor with
  | zero => exact complete
  | succ count ih =>
      unfold MerkleAccumulator.rootFold
      split <;> apply ih <;> exact rawCombine_size _ _

private theorem rootAtDepth_size (tree : MerkleAccumulator.Accumulator Ssz.Bytes)
    (depth : Nat) (complete : ∀ position, (tree.nodes position).size = 32) :
    (MerkleAccumulator.rootAtDepth rawCombine Ssz.zeroChunk tree depth).size = 32 := by
  unfold MerkleAccumulator.rootAtDepth
  split
  · exact advanceZero_size depth Ssz.zeroChunk zero_size
  · apply rootFold_size
    unfold MerkleAccumulator.slot
    split
    · exact complete _
    · exact zero_size

private theorem indexedRoot_size (view : HashLayout.Layout) (position : Nat)
    (arena : Delimited.ArenaState) (root : Ssz.Bytes)
    (success : (HashLayout.indexedRoot view position arena).result = .ok root) : root.size = 32 := by
  apply HashLayout.leafRoot_size _ _ _ _ _ root success
  intro desc value selected cursor child childSuccess
  exact HashLayout.hashTreeRoot_size_raw desc value cursor child childSuccess


-- Keep result projection reasoning separate from the bytes computed by a hash.
private theorem ok_size (node root : Ssz.Bytes)
    (success : (Except.ok node : Except Error Ssz.Bytes) = .ok root)
    (complete : node.size = 32) : root.size = 32 :=
  (congrArg Array.size (Except.ok.inj success)).symm.trans complete

private theorem bind_size {α : Type} (first : Outcome α)
    (next : α → Nat → Outcome Ssz.Bytes)
    (complete : ∀ value used root, (next value used).result = .ok root → root.size = 32)
    (root : Ssz.Bytes) (success : (bind first next).result = .ok root) : root.size = 32 := by
  unfold bind at success
  split at success
  · cases success
  · exact complete _ _ root success

private theorem push_size (tree : MerkleAccumulator.Accumulator Ssz.Bytes)
    (node : Ssz.Bytes) (complete : ∀ position, (tree.nodes position).size = 32)
    (nodeComplete : node.size = 32) :
    ∀ position, ((MerkleAccumulator.push rawCombine Ssz.zeroChunk tree node).1.nodes position).size = 32 := by
  intro position
  unfold MerkleAccumulator.push
  split
  · exact complete position
  · change (if position.val = MerkleAccumulator.trailingOnes tree.count then
        MerkleAccumulator.carry rawCombine Ssz.zeroChunk tree node
          (MerkleAccumulator.trailingOnes tree.count)
      else tree.nodes position).size = 32
    split
    · exact carry_size tree node _ nodeComplete
    · exact complete position
theorem rangeLoop_size_raw (view : HashLayout.Layout) (depth remaining start : Nat)
    (tree : MerkleAccumulator.Accumulator Ssz.Bytes) (arena : Delimited.ArenaState)
    (complete : ∀ position, (tree.nodes position).size = 32) (root : Ssz.Bytes)
    (success : (rangeLoop view depth remaining start tree arena).result = .ok root) : root.size = 32 := by
  induction remaining generalizing start tree arena with
  | zero =>
      simp only [rangeLoop, unchanged, MerkleAccumulator.finishDepth] at success
      split at success
      · cases success
      · cases success
        exact rootAtDepth_size tree depth complete
  | succ remaining ih =>
      simp only [rangeLoop, bind, liftLayout] at success
      cases rooted : (HashLayout.indexedRoot view start arena).result with
      | error reason => simp only [rooted, Except.mapError] at success; cases success
      | ok node =>
          simp only [rooted, Except.mapError, unchanged, MerkleAccumulator.push] at success
          split at success
          · cases success
          · apply ih (start + 1) _ _ _ success
            exact push_size tree node complete (indexedRoot_size view start arena node rooted)

theorem rangeRoot_size_raw (view : HashLayout.Layout) (start stop depth : Nat)
    (arena : Delimited.ArenaState) (root : Ssz.Bytes)
    (success : (rangeRoot view start stop depth arena).result = .ok root) : root.size = 32 :=
  rangeLoop_size_raw view depth (stop - start) start _ arena (fun _ => zero_size) root success

theorem progressiveFrom_size_raw (view : HashLayout.Layout) (start capacity : Nat)
    (positive : 0 < capacity) (arena : Delimited.ArenaState) (root : Ssz.Bytes)
    (success : (progressiveFrom view start capacity positive arena).result = .ok root) : root.size = 32 := by
  rw [progressiveFrom] at success
  split at success
  · apply bind_size _ _ _ root success
    intro left used result returned
    split at returned
    · exact ok_size _ result returned (rawCombine_size _ _)
    · apply bind_size _ _ _ result returned
      intro right used' result' returned'
      exact ok_size _ result' returned' (rawCombine_size _ _)
  · exact ok_size _ root success zero_size

theorem boundedNode_size_raw (view : HashLayout.Layout) (index : NatOperand)
    (depth base treeDepth : Nat) (arena : Delimited.ArenaState) (visit : NodeVisit view)
    (children : ∀ position desc value selected below cursor root,
      (visit position desc value selected below cursor).result = .ok root → root.size = 32)
    (root : Ssz.Bytes) (success : (boundedNode view index depth base treeDepth arena visit).result = .ok root) :
    root.size = 32 := by
  unfold boundedNode at success
  split at success
  · dsimp only at success
    split at success
    · exact ok_size _ root success (advanceZero_size _ _ zero_size)
    · split at success
      · exact rangeRoot_size_raw _ _ _ _ _ root success
      · exact ok_size _ root success (advanceZero_size _ _ zero_size)
  · split at success
    · cases success
    · dsimp only at success
      split at success
      · cases success
      · split at success
        · cases success
        · exact children _ _ _ _ _ _ root success

theorem progressiveNodeFrom_size_raw (view : HashLayout.Layout) (index : NatOperand)
    (visit : NodeVisit view)
    (children : ∀ position desc value selected below cursor root,
      (visit position desc value selected below cursor).result = .ok root → root.size = 32)
    (depth start capacity : Nat) (positive : 0 < capacity) (arena : Delimited.ArenaState)
    (root : Ssz.Bytes)
    (success : (progressiveNodeFrom view index visit depth start capacity positive arena).result = .ok root) :
    root.size = 32 := by
  induction depth generalizing start capacity arena with
  | zero =>
      simp only [progressiveNodeFrom] at success
      split at success
      · exact progressiveFrom_size_raw _ _ _ _ _ root success
      · cases success; exact zero_size
  | succ depth ih =>
      simp only [progressiveNodeFrom] at success
      split at success
      · cases success
      · split at success
        · exact boundedNode_size_raw _ _ _ _ _ _ _ children root success
        · exact ih _ _ _ _ success

private theorem sequence_mixin (element : Codec.Desc) (values : List Codec.Value)
    (positions : Option NatOperand) (mixin : Option Ssz.Bytes) (arena : Delimited.ArenaState)
    (view : HashLayout.Layout)
    (success : (HashLayout.sequence element values positions mixin arena).result = .ok view) :
    view.mixin = mixin := by
  simp only [HashLayout.sequence, HashLayout.bind, HashLayout.lift, HashLayout.unchanged] at success
  repeat' first | rfl | split at success | cases success

theorem layout_mixin_size_raw (desc : Codec.Desc) (value : Codec.Value)
    (arena : Delimited.ArenaState) (view : HashLayout.Layout) (word : Ssz.Bytes)
    (laidOut : (HashLayout.layout desc value arena).result = .ok view)
    (mixed : view.mixin = some word) : word.size = 32 := by
  cases desc with
  | primitive shape =>
      cases shape <;> cases value <;>
        simp only [HashLayout.layout, HashLayout.bind, HashLayout.lift, HashLayout.unchanged] at laidOut
      repeat' first | split at laidOut | cases laidOut
      all_goals dsimp only at mixed
      all_goals simp only [Option.some.injEq, reduceCtorEq] at mixed
      all_goals
        exact (congrArg Array.size mixed).symm.trans (HashLayout.countWord128_size _)
  | vector element length =>
      cases value <;> simp only [HashLayout.layout, HashLayout.unchanged] at laidOut
      repeat' first | split at laidOut | cases laidOut
      all_goals have absent := sequence_mixin _ _ _ _ _ _ laidOut
      all_goals simp_all
  | list element limit =>
      cases value <;> simp only [HashLayout.layout, HashLayout.unchanged] at laidOut
      repeat' first | split at laidOut | cases laidOut
      all_goals have selected := sequence_mixin _ _ _ _ _ _ laidOut
      all_goals
        exact (congrArg Array.size (Option.some.inj (selected.symm.trans mixed))).symm.trans
          (HashLayout.countWord128_size _)
  | progressiveList element limit =>
      cases value <;> simp only [HashLayout.layout, HashLayout.unchanged] at laidOut
      repeat' first | split at laidOut | cases laidOut
      all_goals have selected := sequence_mixin _ _ _ _ _ _ laidOut
      all_goals
        exact (congrArg Array.size (Option.some.inj (selected.symm.trans mixed))).symm.trans
          (HashLayout.countWord128_size _)
  | container fields =>
      cases value <;> simp only [HashLayout.layout, HashLayout.unchanged] at laidOut
      repeat' first | split at laidOut | cases laidOut
      all_goals cases mixed
  | progressiveContainer active fields =>
      cases value <;> simp only [HashLayout.layout, HashLayout.unchanged] at laidOut
      repeat' first | split at laidOut | cases laidOut
      all_goals
        exact (congrArg Array.size (Option.some.inj mixed)).symm.trans
          (MerkleWords.activeFieldsWord_size _)
  | compatibleUnion variants =>
      cases value <;> simp only [HashLayout.layout, HashLayout.unchanged] at laidOut
      repeat' first | split at laidOut | cases laidOut
      all_goals
        exact (congrArg Array.size (Option.some.inj mixed)).symm.trans
          (MerkleWords.lengthWord_size _)

theorem nodeStep_size_raw (desc : Codec.Desc) (value : Codec.Value) (index : NatOperand)
    (depth : Nat) (arena : Delimited.ArenaState) (visit : ValueVisit value)
    (children : ∀ child member childDesc childDepth cursor root,
      (visit child member childDesc childDepth cursor).result = .ok root → root.size = 32)
    (root : Ssz.Bytes) (success : (nodeStep desc value index depth arena visit).result = .ok root) :
    root.size = 32 := by
  simp only [nodeStep] at success
  split at success
  · simp only [liftLayout] at success
    cases rooted : (HashLayout.hashTreeRoot desc value arena).result with
    | error reason => simp only [rooted, Except.mapError] at success; cases success
    | ok node =>
        simp only [rooted, Except.mapError] at success
        have same : node = root := Except.ok.inj success
        subst root
        exact HashLayout.hashTreeRoot_size_raw desc value arena node rooted
  · split at success
    · cases success
    · rename_i view laidOut
      dsimp only at success
      split at success
      · split at success
        · apply boundedNode_size_raw _ _ _ _ _ _ _ _ root success
          intro position childDesc child selected childDepth cursor result childSuccess
          exact children _ _ _ _ _ result childSuccess
        · apply progressiveNodeFrom_size_raw _ _ _ _ _ _ _ _ _ root success
          intro position childDesc child selected childDepth cursor result childSuccess
          exact children _ _ _ _ _ result childSuccess
      · rename_i word mixed
        split at success
        · split at success
          · cases success
          · exact ok_size _ root success
              (layout_mixin_size_raw desc value arena view word laidOut mixed)
        · split at success
          · apply boundedNode_size_raw _ _ _ _ _ _ _ _ root success
            intro position childDesc child selected childDepth cursor result childSuccess
            exact children _ _ _ _ _ result childSuccess
          · apply progressiveNodeFrom_size_raw _ _ _ _ _ _ _ _ _ root success
            intro position childDesc child selected childDepth cursor result childSuccess
            exact children _ _ _ _ _ result childSuccess

theorem nodeAt_size_raw (desc : Codec.Desc) (value : Codec.Value) (index : NatOperand)
    (depth : Nat) (arena : Delimited.ArenaState) (root : Ssz.Bytes)
    (success : (nodeAt desc value index depth arena).result = .ok root) : root.size = 32 := by
  rw [nodeAt] at success
  apply nodeStep_size_raw _ _ _ _ _ _ _ root success
  intro child member childDesc childDepth cursor result childSuccess
  exact nodeAt_size_raw childDesc child index childDepth cursor result childSuccess
termination_by value.nesting
decreasing_by exact Codec.Value.child_nesting_lt _ _ (by assumption)

theorem nodeRoot_size_raw (desc : Codec.Desc) (value : Codec.Value) (index : NatOperand)
    (arena : Delimited.ArenaState) (root : Ssz.Bytes)
    (success : (nodeRoot desc value index arena).result = .ok root) : root.size = 32 := by
  unfold nodeRoot at success
  split at success
  · cases success
  · exact nodeAt_size_raw _ _ _ _ _ root success

end SszNative.Proof

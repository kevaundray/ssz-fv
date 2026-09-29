import SszMerkleAccumulator
import SszMerkleAccumulatorPush
import SszMerkleAccumulatorRoot
import SszMerkleAccumulatorTree

set_option autoImplicit false

namespace SszNative.MerkleAccumulator

variable {α : Type}

/-- A successful public push establishes the occupied-block invariant for the
extended input. Overflow returns the original state instead of entering carry. -/
theorem push_occupied (hash : α → α → α) (zero : α) (chunks : Array α)
    (state : Accumulator α) (node : α) (valid : Occupied hash zero chunks state) :
    if state.count = maxCount then
      push hash zero state node = (state, .error .outputTooSmall)
    else
      (push hash zero state node).2 = .ok () ∧
        Occupied hash zero (chunks.push node) (push hash zero state node).1 := by
  split
  · rename_i full
    exact push_full hash zero state node full
  · rename_i notFull
    have room : state.count < maxCount := by
      have physical := valid.2.1
      unfold Accumulator.Physical at physical
      omega
    rw [push_room hash zero state node room]
    exact ⟨rfl, pushNode_occupied hash zero chunks state node valid room⟩

/-- The physical fixed-array restriction says nothing about the requested depth. -/
theorem rootAtDepth_eq_subtreeAt (chunks : Array Ssz.Bytes)
    (state : Accumulator Ssz.Bytes) (depth : Nat)
    (valid : Occupied Ssz.combine Ssz.zeroChunk chunks state)
    (fits : chunks.size ≤ 2 ^ depth) :
    rootAtDepth Ssz.combine Ssz.zeroChunk state depth = Ssz.subtreeAt chunks depth 0 := by
  rw [subtreeAt_zero_eq]
  exact rootAtDepth_correct Ssz.combine Ssz.zeroChunk chunks state depth valid fits

/-- Full raw-representation capacity/error refinement for a streaming state. -/
theorem finish_refines (chunks : Array Ssz.Bytes) (state : Accumulator Ssz.Bytes)
    (limit : Option NatOperand) (valid : Occupied Ssz.combine Ssz.zeroChunk chunks state) :
    eraseResult (finish Ssz.combine Ssz.zeroChunk state limit) =
      .ok (Ssz.merkleizeBounded chunks (limit.map NatOperand.value)) := by
  have count := valid.1
  have physical : chunks.size < 2 ^ 64 := by
    have bound := valid.2.1
    simp only [Accumulator.Physical, maxCount, treeLevels, count] at bound
    omega
  cases limit with
  | none =>
    have rooted := rootAtDepth_eq_subtreeAt chunks state (Ssz.depthFor chunks.size)
      valid (Ssz.le_two_pow_depthFor chunks.size)
    simp only [finish, boundedDepth, count, depthForCount_eq_depthFor,
      Option.map, Ssz.merkleizeBounded]
    change Except.ok (Except.ok (rootAtDepth Ssz.combine Ssz.zeroChunk state
      (Ssz.depthFor chunks.size))) =
      Except.ok (Except.ok (Ssz.subtreeAt chunks (Ssz.depthFor chunks.size) 0))
    rw [rooted]
  | some capacity =>
    by_cases undersize : capacity.value < chunks.size
    · simp only [finish, boundedDepth, count, Option.map, Ssz.merkleizeBounded,
        undersize, ↓reduceIte]
      change Except.ok (Except.error (Ssz.Err.merkleizeLimit
        (NatOperand.small (BitVec.ofNat 64 chunks.size)).value capacity.value)) =
        Except.ok (Except.error (Ssz.Err.merkleizeLimit chunks.size capacity.value))
      rw [small_value chunks.size physical]
    · have fits : chunks.size ≤ 2 ^ Ssz.depthFor capacity.value :=
        Nat.le_trans (by omega) (Ssz.le_two_pow_depthFor capacity.value)
      have rooted := rootAtDepth_eq_subtreeAt chunks state (Ssz.depthFor capacity.value)
        valid fits
      simp only [finish, boundedDepth, count, Option.map, Ssz.merkleizeBounded,
        undersize, ↓reduceIte, capacityDepth_eq_depthFor]
      change Except.ok (Except.ok (rootAtDepth Ssz.combine Ssz.zeroChunk state
        (Ssz.depthFor capacity.value))) =
        Except.ok (Except.ok (Ssz.subtreeAt chunks (Ssz.depthFor capacity.value) 0))
      rw [rooted]

/-- Exact-depth finishing agrees even on the precise undersized capacity in the
upstream error. The power of two is mathematical and may exceed physical words
on the successful branch. -/
theorem finishDepth_refines (chunks : Array Ssz.Bytes) (state : Accumulator Ssz.Bytes)
    (depth : Nat) (valid : Occupied Ssz.combine Ssz.zeroChunk chunks state) :
    eraseResult (finishDepth Ssz.combine Ssz.zeroChunk state depth) =
      .ok (Ssz.merkleizeBounded chunks (some (2 ^ depth))) := by
  have count := valid.1
  have physical : chunks.size < 2 ^ 64 := by
    have bound := valid.2.1
    simp only [Accumulator.Physical, maxCount, treeLevels, count] at bound
    omega
  by_cases undersize : depth < depthForCount chunks.size
  · have tooMany := (finishDepth_undersize_iff chunks.size depth).1 undersize
    have capacitySmall : 2 ^ depth < 2 ^ 64 := Nat.lt_trans tooMany physical
    simp only [finishDepth, count, undersize, ↓reduceIte, Ssz.merkleizeBounded, tooMany]
    change Except.ok (Except.error (Ssz.Err.merkleizeLimit
      (NatOperand.small (BitVec.ofNat 64 chunks.size)).value
      (NatOperand.small (BitVec.ofNat 64 (2 ^ depth))).value)) =
      Except.ok (Except.error (Ssz.Err.merkleizeLimit chunks.size (2 ^ depth)))
    rw [small_value chunks.size physical, small_value (2 ^ depth) capacitySmall]
  · have fits : chunks.size ≤ 2 ^ depth :=
      (depthForCount_le_iff chunks.size depth).1 (by omega)
    have rooted := rootAtDepth_eq_subtreeAt chunks state depth valid fits
    simp only [finishDepth, count, undersize, ↓reduceIte, Ssz.merkleizeBounded,
      Nat.not_lt.mpr fits, Ssz.depthFor_pow]
    change Except.ok (Except.ok (rootAtDepth Ssz.combine Ssz.zeroChunk state depth)) =
      Except.ok (Except.ok (Ssz.subtreeAt chunks depth 0))
    rw [rooted]

/-- The empty-input fast path agrees with finishing the actual accumulated state. -/
theorem bounded_eq_finish (hash : α → α → α) (zero : α) (chunks : Array α)
    (limit : Option NatOperand) (physical : chunks.size ≤ maxCount) :
    bounded hash zero chunks limit =
      finish hash zero (accumulate hash zero chunks.toList) limit := by
  have count := (accumulate_occupied hash zero chunks physical).1
  by_cases empty : chunks.isEmpty = true
  · have sizeZero : chunks.size = 0 := by simpa [Array.isEmpty] using empty
    have stateZero : (accumulate hash zero chunks.toList).count = 0 := count.trans sizeZero
    simp only [bounded, finish, empty, ↓reduceIte, count]
    congr 1
    funext depth
    simp only [rootAtDepth, stateZero, ↓reduceIte]
  · simp [bounded, finish, count, empty]

/-- The whole allocation-free native algorithm refines upstream bounded
merkleization. No future state, carry, or root equality is assumed. -/
theorem bounded_refines (chunks : Array Ssz.Bytes) (limit : Option NatOperand)
    (physical : chunks.size ≤ maxCount) :
    eraseResult (bounded Ssz.combine Ssz.zeroChunk chunks limit) =
      .ok (Ssz.merkleizeBounded chunks (limit.map NatOperand.value)) := by
  rw [bounded_eq_finish Ssz.combine Ssz.zeroChunk chunks limit physical]
  exact finish_refines chunks (accumulate Ssz.combine Ssz.zeroChunk chunks.toList) limit
    (accumulate_occupied Ssz.combine Ssz.zeroChunk chunks physical)

/-- The native repeated-hash zero loop also refines the upstream cache. -/
theorem zeroSubtree_refines (depth : Nat) :
    zeroSubtree Ssz.combine Ssz.zeroChunk depth = Ssz.zeroSubtree depth := by
  rw [zeroSubtree_eq_zeroRoot, upstream_zeroSubtree_eq_zeroRoot]

end SszNative.MerkleAccumulator

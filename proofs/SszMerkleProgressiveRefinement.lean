import SszMerkleProgressiveInvariant

set_option autoImplicit false

namespace SszNative.MerkleProgressive

variable {α : Type}

theorem progressiveRoot_append_full (hash : α → α → α) (zero : α)
    (block suffix : List α) (level : Nat) (full : block.length = 2 ^ (2 * level)) :
    Ssz.progressiveRoot hash zero (block ++ suffix) level =
      hash (Ssz.subtreeRoot hash (2 * level) (Ssz.padded zero block.toArray))
        (Ssz.progressiveRoot hash zero suffix (level + 1)) := by
  have width : block.length = 4 ^ level := full.trans (width_eq level).symm
  have nonempty : (block ++ suffix).isEmpty = false := by
    cases block with
    | nil => simp only [List.length_nil] at full; have := Nat.two_pow_pos (2 * level); omega
    | cons head tail => rfl
  rw [Ssz.progressiveRoot]
  simp only [nonempty, Bool.false_eq_true, ↓reduceIte]
  rw [← width]
  simp only [List.take_left, List.drop_left]
  rw [full, Ssz.depthFor_pow]

/-- The completed-slot loop is a spine whose open right edge is the current
suffix, not a padded or preallocated full progressive tree. -/
theorem Prefix.fold_correct {hash : α → α → α} {zero : α} {nodes : Fin 32 → α}
    {before : List α} {level : Nat} (valid : Prefix hash zero nodes before level)
    (suffix : List α) :
    foldCompleted hash zero nodes level (Ssz.progressiveRoot hash zero suffix level) =
      Ssz.progressiveRoot hash zero (before ++ suffix) 0 := by
  induction valid generalizing suffix with
  | nil => rfl
  | @snoc chunks block level previous inside full root ih =>
    simp only [foldCompleted, inside, ↓reduceDIte, root]
    rw [← progressiveRoot_append_full hash zero block suffix level full, ih,
      List.append_assoc]

/-- Even at logical width 2^64, the partial current tree ends in a plain zero. -/
theorem progressiveRoot_partial (hash : α → α → α) (zero : α)
    (chunks : List α) (level : Nat) (fits : chunks.length ≤ 2 ^ (2 * level)) :
    Ssz.progressiveRoot hash zero chunks level =
      if chunks.isEmpty then zero else
        hash (Ssz.subtreeRoot hash (2 * level) (Ssz.padded zero chunks.toArray)) zero := by
  have enough : chunks.length ≤ 4 ^ level := by simpa only [width_eq] using fits
  rw [Ssz.progressiveRoot]
  split
  · rfl
  · dsimp only
    rw [List.take_of_length_le enough, List.drop_eq_nil_of_le enough,
      width_eq, Ssz.depthFor_pow, Ssz.progressiveRoot] <;> rfl

theorem finish_correct (hash : α → α → α) (zero : α) (chunks : List α)
    (state : Accumulator α) (valid : Invariant hash zero chunks state) :
    finish hash zero state = Ssz.progressiveRoot hash zero chunks 0 := by
  obtain ⟨_, _, before, pending, decomposition, completed, occupied, pendingFits⟩ := valid
  have currentCount : state.current.count = pending.length := by simpa using occupied.1
  have rooted := MerkleAccumulator.rootAtDepth_correct hash zero pending.toArray
    state.current (2 * state.levels) occupied (by simpa using Nat.le_of_lt pendingFits)
  have tail : (if state.current.count = 0 then zero else
      hash (MerkleAccumulator.rootAtDepth hash zero state.current (2 * state.levels)) zero) =
      Ssz.progressiveRoot hash zero pending state.levels := by
    rw [progressiveRoot_partial hash zero pending state.levels (Nat.le_of_lt pendingFits)]
    cases pending with
    | nil => simp only [List.length_nil] at currentCount; simp only [currentCount, List.isEmpty_nil, ↓reduceIte]
    | cons head rest =>
      have nonzero : state.current.count ≠ 0 := by
        simp only [List.length_cons] at currentCount
        omega
      simp only [nonzero, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, rooted]
  unfold finish
  rw [tail, completed.fold_correct, ← decomposition]

theorem accumulate_correct (hash : α → α → α) (zero : α) (chunks : List α)
    (physical : chunks.length ≤ MerkleAccumulator.maxCount) :
    finish hash zero (accumulate hash zero chunks) =
      Ssz.progressiveRoot hash zero chunks 0 :=
  finish_correct hash zero chunks _ (accumulate_invariant hash zero chunks physical)

theorem progressive_correct (hash : α → α → α) (zero : α) (chunks : Array α)
    (physical : chunks.size ≤ MerkleAccumulator.maxCount) :
    progressive hash zero chunks = Ssz.progressiveRoot hash zero chunks.toList 0 := by
  unfold progressive
  split
  · rename_i empty
    have noLeaves : chunks.toList = [] := by
      have sizeZero : chunks.size = 0 := by simpa only [Array.isEmpty, decide_eq_true_eq] using empty
      apply List.length_eq_zero_iff.mp
      simpa using sizeZero
    rw [noLeaves, Ssz.progressiveRoot] <;> rfl
  · exact accumulate_correct hash zero chunks.toList (by simpa using physical)

/-- Local concrete bridge avoids the upstream proof module's host-specific
elaboration while using the same upstream executable API. -/
theorem upstream_progressive_eq (chunks : List Ssz.Bytes) (level : Nat) :
    Ssz.merkleizeProgressive chunks level =
      Ssz.progressiveRoot Ssz.combine Ssz.zeroChunk chunks level := by
  induction chunks, level using Ssz.merkleizeProgressive.induct with
  | case1 chunks level empty =>
    simp [Ssz.merkleizeProgressive, Ssz.progressiveRoot, empty]
  | case2 chunks level nonempty width ih =>
    rw [Ssz.merkleizeProgressive, Ssz.progressiveRoot]
    simp only [nonempty]
    rw [MerkleAccumulator.subtreeAt_zero_eq, ih]

theorem progressive_refines (chunks : Array Ssz.Bytes)
    (physical : chunks.size ≤ MerkleAccumulator.maxCount) :
    progressive Ssz.combine Ssz.zeroChunk chunks = Ssz.merkleizeProgressive chunks.toList 0 := by
  rw [upstream_progressive_eq]
  exact progressive_correct Ssz.combine Ssz.zeroChunk chunks physical

theorem finish_refines (chunks : List Ssz.Bytes) (state : Accumulator Ssz.Bytes)
    (valid : Invariant Ssz.combine Ssz.zeroChunk chunks state) :
    finish Ssz.combine Ssz.zeroChunk state = Ssz.merkleizeProgressive chunks 0 := by
  rw [upstream_progressive_eq]
  exact finish_correct Ssz.combine Ssz.zeroChunk chunks state valid

theorem progressive_empty (hash : α → α → α) (zero : α) :
    progressive hash zero #[] = zero := rfl

theorem progressive_singleton (hash : α → α → α) (zero node : α) :
    progressive hash zero #[node] = hash node zero := by
  rw [progressive_correct hash zero #[node]
    (by change 1 ≤ MerkleAccumulator.maxCount; decide)]
  change Ssz.progressiveRoot hash zero [node] 0 = hash node zero
  rw [progressiveRoot_partial hash zero [node] 0 (Nat.le_refl 1)] <;> rfl

end SszNative.MerkleProgressive

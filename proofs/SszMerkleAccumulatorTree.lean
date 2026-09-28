import Ssz.Proofs.Merkle.Tree

namespace SszNative.MerkleAccumulator

variable {α : Type}

/-- Only leaves below the subtree's width can affect its root. -/
theorem subtreeRoot_congr (hash : α → α → α) (depth : Nat) {f g : Nat → α}
    (agree : ∀ position, position < 2 ^ depth → f position = g position) :
    Ssz.subtreeRoot hash depth f = Ssz.subtreeRoot hash depth g :=
  Ssz.subtreeRoot_congr hash depth agree

/-- A shifted subtree depends only on its finite interval of leaves. -/
theorem subtreeRoot_shift_congr (hash : α → α → α) (depth start : Nat)
    {f g : Nat → α}
    (agree : ∀ position, start ≤ position → position < start + 2 ^ depth →
      f position = g position) :
    Ssz.subtreeRoot hash depth (fun i => f (start + i)) =
      Ssz.subtreeRoot hash depth (fun i => g (start + i)) := by
  apply Ssz.subtreeRoot_congr hash depth
  intro position below
  exact agree (start + position) (by omega) (by omega)

/-- Joining adjacent equally wide subtrees gives their shifted parent. -/
theorem subtreeRoot_shift_succ (hash : α → α → α) (depth start : Nat)
    (leaves : Nat → α) :
    Ssz.subtreeRoot hash (depth + 1) (fun i => leaves (start + i)) =
      hash (Ssz.subtreeRoot hash depth (fun i => leaves (start + i)))
        (Ssz.subtreeRoot hash depth (fun i => leaves (start + 2 ^ depth + i))) := by
  rw [Ssz.subtreeRoot]
  have shift : (fun i => leaves (start + (i + 2 ^ depth))) =
      (fun i => leaves (start + 2 ^ depth + i)) := by
    funext position
    congr 1
    omega
  rw [shift]

/-- Zero leaves need agree only inside the subtree, not outside it. -/
theorem subtreeRoot_eq_zeroRoot (hash : α → α → α) (zero : α) (depth : Nat)
    {leaves : Nat → α}
    (empty : ∀ position, position < 2 ^ depth → leaves position = zero) :
    Ssz.subtreeRoot hash depth leaves = Ssz.zeroRoot hash zero depth := by
  rw [← Ssz.subtreeRoot_const_zero hash zero depth]
  exact Ssz.subtreeRoot_congr hash depth empty

/-- A padded array reads zero once its data has ended. -/
theorem padded_eq_zero_of_size_le (zero : α) (chunks : Array α) {position : Nat}
    (past : chunks.size ≤ position) : Ssz.padded zero chunks position = zero := by
  simp only [Ssz.padded, Array.getElem?_eq_none past, Option.getD_none]

/-- Appending a node does not replace an existing array leaf. -/
theorem padded_push_of_lt (zero : α) (chunks : Array α) (value : α) {position : Nat}
    (before : position < chunks.size) :
    Ssz.padded zero (chunks.push value) position = Ssz.padded zero chunks position := by
  simp only [Ssz.padded, Array.getElem?_push, if_neg (Nat.ne_of_lt before)]

/-- The newly appended leaf is read at the old array end. -/
theorem padded_push_at_size (zero : α) (chunks : Array α) (value : α) :
    Ssz.padded zero (chunks.push value) chunks.size = value := by
  simp only [Ssz.padded, Array.getElem?_push, if_pos rfl, Option.getD_some]

/-- The depth-zero subtree at the previous end is the newly appended node. -/
theorem subtreeRoot_padded_push_leaf (hash : α → α → α) (zero : α)
    (chunks : Array α) (value : α) :
    Ssz.subtreeRoot hash 0
        (fun i => Ssz.padded zero (chunks.push value) (chunks.size + i)) = value := by
  simpa only [Ssz.subtreeRoot, Nat.add_zero] using padded_push_at_size zero chunks value

/-- A completed subtree is unchanged by a later array append. -/
theorem subtreeRoot_padded_push (hash : α → α → α) (zero : α)
    (chunks : Array α) (value : α) (depth start : Nat)
    (before : start + 2 ^ depth ≤ chunks.size) :
    Ssz.subtreeRoot hash depth (fun i => Ssz.padded zero (chunks.push value) (start + i)) =
      Ssz.subtreeRoot hash depth (fun i => Ssz.padded zero chunks (start + i)) := by
  apply Ssz.subtreeRoot_congr hash depth
  intro position below
  exact padded_push_of_lt zero chunks value (by omega)

/-- List and array padding expose the same leaf function. -/
theorem padded_toArray_eq_getD (zero : α) (chunks : List α) (position : Nat) :
    Ssz.padded zero chunks.toArray position = chunks.getD position zero := by
  simp [Ssz.padded, List.getD]

/-- A completed subtree is unchanged when a list receives one more leaf. -/
theorem subtreeRoot_list_append_singleton (hash : α → α → α) (zero : α)
    (chunks : List α) (value : α) (depth start : Nat)
    (before : start + 2 ^ depth ≤ chunks.length) :
    Ssz.subtreeRoot hash depth (fun i => (chunks ++ [value]).getD (start + i) zero) =
      Ssz.subtreeRoot hash depth (fun i => chunks.getD (start + i) zero) := by
  apply Ssz.subtreeRoot_congr hash depth
  intro position below
  simp only [List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by omega : start + position < chunks.length)]

/-- The array view of a list has the same completed-subtree append law. -/
theorem subtreeRoot_padded_append_singleton (hash : α → α → α) (zero : α)
    (chunks : List α) (value : α) (depth start : Nat)
    (before : start + 2 ^ depth ≤ chunks.length) :
    Ssz.subtreeRoot hash depth
        (fun i => Ssz.padded zero (chunks ++ [value]).toArray (start + i)) =
      Ssz.subtreeRoot hash depth (fun i => Ssz.padded zero chunks.toArray (start + i)) := by
  simpa only [padded_toArray_eq_getD] using
    subtreeRoot_list_append_singleton hash zero chunks value depth start before

/-- A shifted subtree entirely beyond the array is the corresponding zero root. -/
theorem subtreeRoot_padded_past_data (hash : α → α → α) (zero : α) (depth : Nat)
    (chunks : Array α) {start : Nat} (past : chunks.size ≤ start) :
    Ssz.subtreeRoot hash depth (fun i => Ssz.padded zero chunks (start + i)) =
      Ssz.zeroRoot hash zero depth :=
  Ssz.subtreeRoot_padded_past_data hash zero depth chunks past

/-- The same zero-subtree law holds for the list representation of accumulated leaves. -/
theorem subtreeRoot_list_past_data (hash : α → α → α) (zero : α) (depth : Nat)
    (chunks : List α) {start : Nat} (past : chunks.length ≤ start) :
    Ssz.subtreeRoot hash depth (fun i => chunks.getD (start + i) zero) =
      Ssz.zeroRoot hash zero depth := by
  have arrayPast : chunks.toArray.size ≤ start := by simpa using past
  simpa only [padded_toArray_eq_getD] using
    Ssz.subtreeRoot_padded_past_data hash zero depth chunks.toArray arrayPast

/-- The cached SSZ walk is the abstract root over the same shifted padded leaves. -/
theorem subtreeAt_eq_subtreeRoot (chunks : Array Ssz.Bytes) (depth start : Nat) :
    Ssz.subtreeAt chunks depth start =
      Ssz.subtreeRoot Ssz.combine depth (fun i => Ssz.padded Ssz.zeroChunk chunks (start + i)) :=
  Ssz.subtreeAt_eq_subtreeRoot chunks depth start

/-- SSZ's cache agrees with the abstract zero tree at every depth, without a cache bound. -/
theorem upstream_zeroSubtree_eq_zeroRoot (depth : Nat) :
    Ssz.zeroSubtree depth = Ssz.zeroRoot Ssz.combine Ssz.zeroChunk depth :=
  Ssz.zeroSubtree_eq depth

end SszNative.MerkleAccumulator

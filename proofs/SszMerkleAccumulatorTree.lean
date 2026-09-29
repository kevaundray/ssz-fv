import Ssz.Merkle.Tree
import Ssz.Proofs.Merkle.Merkleize

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
  simp only [Ssz.padded, Array.getElem?_push]
  split
  · rename_i atEnd
    exact False.elim (Nat.ne_of_lt before atEnd)
  · rfl

/-- The newly appended leaf is read at the old array end. -/
theorem padded_push_at_size (zero : α) (chunks : Array α) (value : α) :
    Ssz.padded zero (chunks.push value) chunks.size = value := by
  simp only [Ssz.padded, Array.getElem?_push_size, Option.getD_some]

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

private theorem upstream_zeroRootsUpTo_size (built : Nat) :
    (Ssz.zeroRootsUpTo built).size = built + 1 := by
  induction built with
  | zero => rfl
  | succ built ih => simp only [Ssz.zeroRootsUpTo, Array.size_push, ih]

private theorem upstream_zeroRootsUpTo_get (built : Nat) :
    ∀ depth, depth ≤ built →
      (Ssz.zeroRootsUpTo built)[depth]?.getD Ssz.zeroChunk =
        Ssz.zeroRoot Ssz.combine Ssz.zeroChunk depth := by
  induction built with
  | zero =>
    intro depth holds
    have atZero : depth = 0 := by omega
    subst depth
    rfl
  | succ built ih =>
    intro depth holds
    have size : (Ssz.zeroRootsUpTo built).size = built + 1 :=
      upstream_zeroRootsUpTo_size built
    rcases Nat.lt_or_ge depth (built + 1) with below | atTop
    · have different : depth ≠ (Ssz.zeroRootsUpTo built).size := by omega
      rw [Ssz.zeroRootsUpTo, Array.getElem?_push]
      split
      · rename_i atEnd
        exact False.elim (different atEnd)
      · exact ih depth (by omega)
    · have top : depth = built + 1 := by omega
      subst depth
      rw [Ssz.zeroRootsUpTo, Array.getElem?_push]
      split
      · simp only [Option.getD_some, Ssz.zeroRoot, ih built (Nat.le_refl built)]
      · rename_i different
        exact False.elim (different size.symm)

/-- SSZ's cache agrees with the abstract zero tree at every depth, without a cache bound. -/
theorem upstream_zeroSubtree_eq_zeroRoot (depth : Nat) :
    Ssz.zeroSubtree depth = Ssz.zeroRoot Ssz.combine Ssz.zeroChunk depth := by
  by_cases covered : depth ≤ Ssz.maxZeroDepth
  · have present : depth < Ssz.zeroRoots.size := by
      change depth < (Ssz.zeroRootsUpTo Ssz.maxZeroDepth).size
      rw [upstream_zeroRootsUpTo_size]
      omega
    have entry := upstream_zeroRootsUpTo_get Ssz.maxZeroDepth depth covered
    change Ssz.zeroRoots[depth]?.getD Ssz.zeroChunk =
      Ssz.zeroRoot Ssz.combine Ssz.zeroChunk depth at entry
    simpa only [Ssz.zeroSubtree, Array.getElem?_eq_getElem present, Option.getD_some]
      using entry
  · have absent : Ssz.zeroRoots[depth]? = none := Array.getElem?_eq_none (by
      change (Ssz.zeroRootsUpTo Ssz.maxZeroDepth).size ≤ depth
      rw [upstream_zeroRootsUpTo_size]
      omega)
    simp only [Ssz.zeroSubtree, absent]

/-- The cached SSZ walk is the abstract root over the same shifted padded leaves. -/
theorem subtreeAt_eq_subtreeRoot (chunks : Array Ssz.Bytes) (depth start : Nat) :
    Ssz.subtreeAt chunks depth start =
      Ssz.subtreeRoot Ssz.combine depth
        (fun i => Ssz.padded Ssz.zeroChunk chunks (start + i)) := by
  induction depth generalizing start with
  | zero =>
    unfold Ssz.subtreeAt
    split
    · rename_i past
      rw [upstream_zeroSubtree_eq_zeroRoot]
      simpa only [Ssz.subtreeRoot, Ssz.zeroRoot, Nat.add_zero] using
        (padded_eq_zero_of_size_le Ssz.zeroChunk chunks past).symm
    · rfl
  | succ depth ih =>
    unfold Ssz.subtreeAt
    split
    · rename_i past
      rw [upstream_zeroSubtree_eq_zeroRoot]
      exact (Ssz.subtreeRoot_padded_past_data Ssz.combine Ssz.zeroChunk
        (depth + 1) chunks past).symm
    · change Ssz.combine (Ssz.subtreeAt chunks depth start)
          (Ssz.subtreeAt chunks depth (start + 2 ^ depth)) = _
      rw [ih start, ih (start + 2 ^ depth)]
      exact (subtreeRoot_shift_succ Ssz.combine depth start
        (Ssz.padded Ssz.zeroChunk chunks)).symm

/-- Starting the concrete walk at zero gives the unshifted padded root. -/
theorem subtreeAt_zero_eq (chunks : Array Ssz.Bytes) {depth : Nat} :
    Ssz.subtreeAt chunks depth 0 =
      Ssz.subtreeRoot Ssz.combine depth (Ssz.padded Ssz.zeroChunk chunks) := by
  simpa only [Nat.zero_add] using subtreeAt_eq_subtreeRoot chunks depth 0

end SszNative.MerkleAccumulator

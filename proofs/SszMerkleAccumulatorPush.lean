import SszMerkleAccumulatorPushArithmetic
import SszMerkleAccumulatorTree

namespace SszNative.MerkleAccumulator

variable {α : Type}

/-- Every carry step joins the old completed left block to the newly completed
right block. The hypothesis mentions only the original state's occupied bits. -/
theorem carry_subtree (hash : α → α → α) (zero : α) (chunks : Array α)
    (state : Accumulator α) (node : α) (valid : Occupied hash zero chunks state)
    (height : Nat) (bounded : height ≤ 64)
    (ones : ∀ index, index < height → state.count.testBit index = true) :
    carry hash zero state node height = Ssz.subtreeRoot hash height
      (fun index => Ssz.padded zero (chunks.push node)
        (state.count / 2 ^ height * 2 ^ height + index)) := by
  induction height with
  | zero =>
      simpa only [carry, Nat.pow_zero, Nat.div_one, Nat.mul_one, valid.1] using
        (subtreeRoot_padded_push_leaf hash zero chunks node).symm
  | succ height ih =>
      have inside : height < 64 := by omega
      have bit : state.count.testBit height = true := ones height (by omega)
      have before : state.count / 2 ^ (height + 1) * 2 ^ (height + 1) +
          2 ^ height ≤ chunks.size := by
        rw [← valid.1]
        exact occupied_block_before state.count height bit
      have left := valid.2.2 ⟨height, inside⟩ bit
      have origin := block_base_of_bit state.count height true bit
      simp only [Bool.toNat_true, Nat.one_mul] at origin
      rw [carry, subtreeRoot_shift_succ]
      congr 1
      · simp only [slot, inside, ↓reduceDIte]
        exact left.trans (subtreeRoot_padded_push hash zero chunks node height
          (state.count / 2 ^ (height + 1) * 2 ^ (height + 1)) before).symm
      · rw [ih (by omega) (fun index below => ones index (by omega)), origin]

/-- The actual bounded native-style carry and single-cell write preserve the
completed-subtree invariant; no post-state or carry result is assumed. -/
theorem pushNode_occupied (hash : α → α → α) (zero : α) (chunks : Array α)
    (state : Accumulator α) (node : α) (valid : Occupied hash zero chunks state)
    (room : state.count < maxCount) :
    Occupied hash zero (chunks.push node) (pushNode hash zero state node) := by
  obtain ⟨bound, ones, stop⟩ := trailingOnes_spec state.count room
  refine ⟨?_, ?_, ?_⟩
  · simpa only [pushNode_count, Array.size_push] using congrArg (· + 1) valid.1
  · change state.count + 1 ≤ maxCount
    omega
  · intro index present
    change (state.count + 1).testBit index.val = true at present
    have not_below : trailingOnes state.count ≤ index.val := by
      apply Decidable.byContradiction
      intro below
      have cleared := succ_testBit_below_run state.count (trailingOnes state.count)
        index.val ones (by omega)
      rw [cleared] at present
      contradiction
    by_cases same : index.val = trailingOnes state.count
    · change (if index.val = trailingOnes state.count then
          carry hash zero state node (trailingOnes state.count) else state.nodes index) =
        Ssz.subtreeRoot hash index.val (fun position => Ssz.padded zero (chunks.push node)
          ((state.count + 1) / 2 ^ (index.val + 1) * 2 ^ (index.val + 1) + position))
      simp only [same, ↓reduceIte]
      rw [
        carry_subtree hash zero chunks state node valid (trailingOnes state.count)
          (by omega) ones]
      have quotient := succ_div_pow_eq state.count (trailingOnes state.count)
        (trailingOnes state.count + 1) stop (by omega)
      have origin := block_base_of_bit state.count (trailingOnes state.count) false stop
      simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at origin
      rw [quotient, origin]
    · have above : trailingOnes state.count < index.val := by omega
      have old_bit : state.count.testBit index.val = true := by
        rw [succ_testBit_above_run state.count (trailingOnes state.count)
          index.val stop above] at present
        exact present
      rw [pushNode_unchanged hash zero state node index same, valid.2.2 index old_bit]
      change Ssz.subtreeRoot hash index.val
          (fun position => Ssz.padded zero chunks
            (state.count / 2 ^ (index.val + 1) * 2 ^ (index.val + 1) + position)) =
        Ssz.subtreeRoot hash index.val
          (fun position => Ssz.padded zero (chunks.push node)
            ((state.count + 1) / 2 ^ (index.val + 1) * 2 ^ (index.val + 1) + position))
      rw [succ_div_pow_eq state.count (trailingOnes state.count) (index.val + 1)
        stop (by omega)]
      apply (subtreeRoot_padded_push hash zero chunks node index.val
        (state.count / 2 ^ (index.val + 1) * 2 ^ (index.val + 1)) ?_).symm
      rw [← valid.1]
      exact occupied_block_before state.count index.val old_bit

/-- A physically bounded suffix may be folded onto any valid accumulator. -/
theorem foldl_occupied (hash : α → α → α) (zero : α) (chunks : Array α)
    (state : Accumulator α) (suffix : List α) (valid : Occupied hash zero chunks state)
    (physical : chunks.size + suffix.length ≤ maxCount) :
    Occupied hash zero (chunks.toList ++ suffix).toArray
      (suffix.foldl (pushNode hash zero) state) := by
  induction suffix generalizing chunks state with
  | nil => simpa using valid
  | cons node suffix ih =>
      have room : state.count < maxCount := by
        have count_eq := valid.1
        simp only [List.length_cons] at physical
        omega
      have pushed := pushNode_occupied hash zero chunks state node valid room
      have capacity : (chunks.push node).size + suffix.length ≤ maxCount := by
        simpa only [Array.size_push, List.length_cons, Nat.add_assoc,
          Nat.add_comm 1 suffix.length] using physical
      have rest := ih (chunks.push node) (pushNode hash zero state node) pushed capacity
      simpa only [Array.toList_push, List.append_assoc, List.singleton_append,
        List.foldl_cons] using rest

/-- Every physically representable leaf array establishes the invariant by
executing the list fold of actual pushes, starting from the empty state. -/
theorem accumulate_occupied (hash : α → α → α) (zero : α) (chunks : Array α)
    (physical : chunks.size ≤ maxCount) :
    Occupied hash zero chunks (accumulate hash zero chunks.toList) := by
  have result := foldl_occupied hash zero #[] (new zero) chunks.toList
    (new_occupied hash zero) (by simpa using physical)
  simpa [accumulate] using result

end SszNative.MerkleAccumulator

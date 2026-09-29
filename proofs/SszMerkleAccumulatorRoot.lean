import SszMerkleAccumulatorRootArithmetic
import SszMerkleAccumulatorTree

namespace SszNative.MerkleAccumulator

variable {α : Type}

/-- A cursor denotes the zero tree at its own depth; advancing it does not
materialize any tree and does not assume a bound on the requested depth. -/
theorem root_cursor_advance (hash : α → α → α) (zero : α)
    (cursor : ZeroCursor α) (height : Nat)
    (correct : cursor.node = zeroSubtree hash zero cursor.depth)
    (below : cursor.depth ≤ height) :
    advanceZero hash (height - cursor.depth) cursor.node = zeroSubtree hash zero height := by
  rw [correct]
  unfold zeroSubtree
  rw [← advanceZero_add]
  have levels : cursor.depth + (height - cursor.depth) = height := by omega
  rw [levels]

/-- The live node is the aligned subtree containing the last real leaf.
The boundary premise describes only the current count bits, never a future root.
Every occupied-slot access is justified by its concrete index below 64. -/
theorem rootFold_correct (hash : α → α → α) (zero : α) (chunks : Array α)
    (state : Accumulator α) (valid : Occupied hash zero chunks state)
    (physical : state.count < 2 ^ 64)
    (height fuel : Nat) (node : α) (cursor : ZeroCursor α)
    (boundary : 0 < state.count % 2 ^ (height + 1))
    (nodeCorrect : node = Ssz.subtreeRoot hash height
      (fun index => Ssz.padded zero chunks (rootBlock (state.count - 1) height + index)))
    (cursorCorrect : cursor.node = zeroSubtree hash zero cursor.depth)
    (cursorBelow : cursor.depth ≤ height) :
    rootFold hash zero state (state.count &&& (state.count - 1)) height fuel node cursor =
      Ssz.subtreeRoot hash (height + fuel)
        (fun index => Ssz.padded zero chunks
          (rootBlock (state.count - 1) (height + fuel) + index)) := by
  induction fuel generalizing height node cursor with
  | zero => simpa only [rootFold, Nat.add_zero] using nodeCorrect
  | succ fuel ih =>
      have nextBoundary := root_boundary_succ state.count height boundary
      by_cases bit : (state.count - 1).testBit height = true
      · have branch := (root_remaining_branch state.count height physical boundary).2 bit
        have occupiedBit : state.count.testBit height = true := by
          have remainder := branch.2
          simp only [Nat.testBit_and, Bool.and_eq_true] at remainder
          exact remainder.1
        have origin : state.count / 2 ^ (height + 1) * 2 ^ (height + 1) =
            rootBlock (state.count - 1) (height + 1) := by
          unfold rootBlock
          rw [root_pred_div state.count (2 ^ (height + 1)) (Nat.two_pow_pos _) boundary]
        have slotCorrect : slot zero state height = Ssz.subtreeRoot hash height
            (fun index => Ssz.padded zero chunks
              (rootBlock (state.count - 1) (height + 1) + index)) := by
          simp only [slot, branch.1, ↓reduceDIte]
          rw [valid.2.2 ⟨height, branch.1⟩ occupiedBit, origin]
        have nextNode : hash (slot zero state height) node =
            Ssz.subtreeRoot hash (height + 1)
              (fun index => Ssz.padded zero chunks
                (rootBlock (state.count - 1) (height + 1) + index)) := by
          rw [slotCorrect, nodeCorrect, rootBlock_step_true (state.count - 1) height bit]
          exact (subtreeRoot_shift_succ hash height
            (rootBlock (state.count - 1) (height + 1)) (Ssz.padded zero chunks)).symm
        simp only [rootFold, branch, true_and, ↓reduceIte]
        have result := ih (height + 1) (hash (slot zero state height) node) cursor
          nextBoundary nextNode cursorCorrect (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result
      · have branch : ¬(height < 64 ∧
            (state.count &&& (state.count - 1)).testBit height = true) := by
          intro condition
          exact bit ((root_remaining_branch state.count height physical boundary).1 condition)
        have clear : (state.count - 1).testBit height = false := by
          cases value : (state.count - 1).testBit height <;> simp_all
        have same := rootBlock_step_false (state.count - 1) height clear
        have paddingCorrect := root_cursor_advance hash zero cursor height cursorCorrect cursorBelow
        have last := Nat.lt_div_mul_add (a := state.count - 1) (Nat.two_pow_pos height)
        have past : chunks.size ≤ rootBlock (state.count - 1) height + 2 ^ height := by
          change state.count - 1 < rootBlock (state.count - 1) height + 2 ^ height at last
          have countEq := valid.1
          omega
        have rightRoot := subtreeRoot_padded_past_data hash zero height chunks past
        have nextNode : hash node (advanceZero hash (height - cursor.depth) cursor.node) =
            Ssz.subtreeRoot hash (height + 1)
              (fun index => Ssz.padded zero chunks
                (rootBlock (state.count - 1) (height + 1) + index)) := by
          rw [subtreeRoot_shift_succ, ← same, ← nodeCorrect, rightRoot,
            paddingCorrect, zeroSubtree_eq_zeroRoot]
        simp only [rootFold, branch, ↓reduceIte]
        have result := ih (height + 1)
          (hash node (advanceZero hash (height - cursor.depth) cursor.node))
          ⟨advanceZero hash (height - cursor.depth) cursor.node, height⟩
          nextBoundary nextNode paddingCorrect (by simp)
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

/-- The native-style trailing-zero scan and occupied-left fold return the
padded SSZ root. Logical depth is unbounded; only the stored count is physical.
An empty accumulator uses the zero loop, while a complete tree returns its
occupied cell without invoking the zero cursor. -/
theorem rootAtDepth_correct (hash : α → α → α) (zero : α) (chunks : Array α)
    (state : Accumulator α) (depth : Nat)
    (valid : Occupied hash zero chunks state) (fits : chunks.size ≤ 2 ^ depth) :
    rootAtDepth hash zero state depth = Ssz.subtreeRoot hash depth (Ssz.padded zero chunks) := by
  have countEq := valid.1
  by_cases empty : state.count = 0
  · simp only [rootAtDepth, empty, ↓reduceIte, zeroSubtree_eq_zeroRoot]
    symm
    have past : chunks.size ≤ 0 := by omega
    simpa only [Nat.zero_add] using
      subtreeRoot_padded_past_data hash zero depth chunks (start := 0) past
  · have physical : state.count < 2 ^ 64 := by
      have bound := valid.2.1
      change state.count ≤ 2 ^ 64 - 1 at bound
      have positive := Nat.two_pow_pos 64
      omega
    obtain ⟨below, bit, clear⟩ := trailingZeros_spec state.count empty physical
    obtain ⟨initialBlock, boundary, powerBelow⟩ :=
      root_initial_block state.count (trailingZeros state.count) clear bit
    have heightBelow : trailingZeros state.count ≤ depth := by
      apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1
      omega
    have initialNode : slot zero state (trailingZeros state.count) =
        Ssz.subtreeRoot hash (trailingZeros state.count)
          (fun index => Ssz.padded zero chunks
            (rootBlock (state.count - 1) (trailingZeros state.count) + index)) := by
      simp only [slot, below, ↓reduceDIte]
      rw [valid.2.2 ⟨trailingZeros state.count, below⟩ bit, initialBlock]
    have result := rootFold_correct hash zero chunks state valid physical
      (trailingZeros state.count) (depth - trailingZeros state.count)
      (slot zero state (trailingZeros state.count)) ⟨zero, 0⟩
      boundary initialNode rfl (Nat.zero_le _)
    have finalHeight : trailingZeros state.count + (depth - trailingZeros state.count) = depth := by
      omega
    have finalIndex : state.count - 1 < 2 ^ depth := by omega
    have finalBlock : rootBlock (state.count - 1) depth = 0 := by
      unfold rootBlock
      rw [Nat.div_eq_of_lt finalIndex, Nat.zero_mul]
    simp only [rootAtDepth, empty, ↓reduceIte]
    simpa only [finalHeight, finalBlock, Nat.zero_add] using result

end SszNative.MerkleAccumulator

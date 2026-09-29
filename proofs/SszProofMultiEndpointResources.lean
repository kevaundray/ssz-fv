import SszProofMultiResources
import SszProofWidthResources
import SszIndicesFrontierResourcesRuns

set_option autoImplicit false

namespace SszNative.Proof

def CursorBounds (arena : Delimited.ArenaState) (used : Nat) : Prop :=
  arena.used ≤ used ∧ used ≤ arena.capacity

theorem cursorBounds_of_safe (arena : Delimited.ArenaState) (used : Nat)
    (safe : HashLayout.CursorSafe arena used)
    (valid : Arena.Valid arena.base arena.capacity arena.used) : CursorBounds arena used :=
  ⟨safe.1, (safe.2 valid).2.2.2⟩

theorem bind_cursorBounds {α β : Type} (arena : Delimited.ArenaState)
    (first : Outcome α) (next : α → Nat → Outcome β)
    (valid : Arena.Valid arena.base arena.capacity arena.used)
    (before : CursorBounds arena first.used)
    (after : ∀ value used, Arena.Valid arena.base arena.capacity used →
      CursorBounds { arena with used := used } (next value used).used) :
    CursorBounds arena (bind first next).used := by
  cases result : first.result with
  | error reason => simpa only [bind, result] using before
  | ok value =>
      have later := after value first.used ⟨valid.1, valid.2.1, valid.2.2.1, before.2⟩
      simp only [bind, result]
      exact ⟨Nat.le_trans before.1 later.1, later.2⟩

theorem multiReserved_cursor_bounds (leaves proof : List Ssz.Bytes)
    (indices helpers : List NatOperand) (leafCount : leaves.length = indices.length)
    (proofCount : proof.length = helpers.length) (nodeLayout : TypedArena.Layout)
    (arena : Delimited.ArenaState) (valid : Arena.Valid arena.base arena.capacity arena.used) :
    CursorBounds arena (multiReserved leaves proof indices helpers leafCount proofCount nodeLayout arena).used := by
  -- Keep the fold opaque: its result never changes the committed reservation cursor.
  by_cases count : indices.length + helpers.length < 2^64
  · cases reserved : TypedArena.reserve nodeLayout arena.base arena.capacity arena.used
      (indices.length + helpers.length) with
    | none =>
        rw [multiReserved_reservation_failure leaves proof indices helpers leafCount proofCount
          nodeLayout arena count reserved]
        exact ⟨Nat.le_refl _, valid.2.2.2⟩
    | some allocated =>
        rw [(multiReserved_initialized leaves proof indices helpers leafCount proofCount
          nodeLayout arena allocated count reserved).1]
        exact TypedArena.reserve_cursor_bounds nodeLayout arena.base arena.capacity arena.used
          (indices.length + helpers.length) valid allocated reserved
  · rw [multiReserved_count_failure leaves proof indices helpers leafCount proofCount
      nodeLayout arena count]
    exact ⟨Nat.le_refl _, valid.2.2.2⟩

theorem calculateMultiMerkleRoot_cursor_bounds (leaves proof : List Ssz.Bytes)
    (indices : List NatOperand) (nodeLayout : TypedArena.Layout) (arena : Delimited.ArenaState)
    (valid : Arena.Valid arena.base arena.capacity arena.used) :
    CursorBounds arena (calculateMultiMerkleRoot leaves proof indices nodeLayout arena).used := by
  unfold calculateMultiMerkleRoot
  split
  · rename_i leafCount
    apply bind_cursorBounds _ _ _ valid
    · exact Indices.helperIndices_cursor_bounds indices arena.base arena.capacity arena.used valid
    · intro helpers used valid'
      split
      · rename_i proofCount
        exact multiReserved_cursor_bounds leaves proof indices helpers.values leafCount proofCount
          nodeLayout { arena with used := used } valid'
      · exact cursorBounds_of_safe _ _ (failCount_cursorSafe _ _ _ _) valid'
  · exact cursorBounds_of_safe _ _ (failCount_cursorSafe _ _ _ _) valid

theorem verifyMerkleMultiproof_cursor_bounds (leaves proof : List Ssz.Bytes)
    (indices : List NatOperand) (root : Ssz.Bytes) (nodeLayout : TypedArena.Layout)
    (arena : Delimited.ArenaState) (valid : Arena.Valid arena.base arena.capacity arena.used) :
    CursorBounds arena (verifyMerkleMultiproof leaves proof indices root nodeLayout arena).used := by
  unfold verifyMerkleMultiproof
  apply bind_cursorBounds _ _ _ valid (cursorBounds_of_safe _ _ (checkChunk_cursorSafe _ _) valid)
  intro rootCheck used valid'
  apply bind_cursorBounds _ _ _ valid'
    (cursorBounds_of_safe _ _ (checkChunks_cursorSafe _ _) valid')
  intro leafCheck used' valid''
  apply bind_cursorBounds _ _ _ valid''
    (cursorBounds_of_safe _ _ (checkChunks_cursorSafe _ _) valid'')
  intro proofCheck used'' valid'''
  apply bind_cursorBounds _ _ _ valid'''
    (calculateMultiMerkleRoot_cursor_bounds leaves proof indices nodeLayout _ valid''')
  intro actual used''' valid''''
  exact ⟨Nat.le_refl _, valid''''.2.2.2⟩

theorem verifyMerkleMultiproof_leaves_error (leaves proof : List Ssz.Bytes)
    (indices : List NatOperand) (root : Ssz.Bytes) (nodeLayout : TypedArena.Layout)
    (arena : Delimited.ArenaState) (rootWidth : root.size = 32) (reason : Error)
    (failed : (checkChunks leaves arena).result = .error reason) :
    verifyMerkleMultiproof leaves proof indices root nodeLayout arena =
      ⟨.error reason, (checkChunks leaves arena).used, (checkChunks leaves arena).effects⟩ := by
  unfold verifyMerkleMultiproof
  rw [checkChunk_width root arena rootWidth, bind_unchanged]
  simp only [bind, failed]

theorem verifyMerkleMultiproof_helpers_error (leaves proof : List Ssz.Bytes)
    (indices : List NatOperand) (root : Ssz.Bytes) (nodeLayout : TypedArena.Layout)
    (arena : Delimited.ArenaState) (rootWidth : root.size = 32)
    (leafWidths : ∀ node ∈ leaves, node.size = 32) (reason : Error)
    (failed : (checkChunks proof arena).result = .error reason) :
    verifyMerkleMultiproof leaves proof indices root nodeLayout arena =
      ⟨.error reason, (checkChunks proof arena).used, (checkChunks proof arena).effects⟩ := by
  unfold verifyMerkleMultiproof
  rw [checkChunk_width root arena rootWidth, bind_unchanged,
    checkChunks_widths leaves arena leafWidths, bind_unchanged]
  simp only [bind, failed]

theorem verifyMerkleMultiproof_reconstruction_error (leaves proof : List Ssz.Bytes)
    (indices : List NatOperand) (root : Ssz.Bytes) (nodeLayout : TypedArena.Layout)
    (arena : Delimited.ArenaState) (rootWidth : root.size = 32)
    (leafWidths : ∀ node ∈ leaves, node.size = 32)
    (proofWidths : ∀ node ∈ proof, node.size = 32) (reason : Error)
    (failed : (calculateMultiMerkleRoot leaves proof indices nodeLayout arena).result = .error reason) :
    verifyMerkleMultiproof leaves proof indices root nodeLayout arena =
      ⟨.error reason, (calculateMultiMerkleRoot leaves proof indices nodeLayout arena).used,
        (calculateMultiMerkleRoot leaves proof indices nodeLayout arena).effects⟩ := by
  rw [verifyMerkleMultiproof_widths leaves proof indices root nodeLayout arena
    rootWidth leafWidths proofWidths]
  simp only [bind, failed]

end SszNative.Proof

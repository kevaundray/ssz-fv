import SszProofMulti

set_option autoImplicit false

namespace SszNative.Proof

def MultiNode.view {l p : Nat} (node : MultiNode l p) : NatOperand × Nat × Nat :=
  (node.index, node.shift, node.depth)

/-- Every original borrowed integer and both view counters survive the entire
value pass, including the initialized prefix retained on a missing sibling. -/
theorem multiPassWorker_views {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (deepest : Nat)
    (pending : List (MultiNode l p)) :
    ∀ doneRev, (multiPassWorker leaves proof hl hp deepest doneRev pending).nodes.map
      MultiNode.view = (doneRev.reverse ++ pending).map MultiNode.view := by
  induction pending with
  | nil => intro doneRev; simp only [multiPassWorker, List.append_nil]
  | cons node pending ih =>
      intro doneRev
      unfold multiPassWorker
      split
      · simpa [List.reverse_cons, List.append_assoc] using ih (node :: doneRev)
      · split
        · rfl
        · rename_i sibling found
          split
          · simpa [List.reverse_cons, List.append_assoc] using ih (node :: doneRev)
          · let updated : MultiNode l p := { node with
              value := (.hashed (rawCombine (node.value.bytes leaves proof hl hp)
                (sibling.value.bytes leaves proof hl hp))) }
            simpa [updated, MultiNode.view, List.reverse_cons, List.map_append,
              List.append_assoc] using ih (updated :: doneRev)

theorem multiPass_views {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (deepest : Nat)
    (nodes : List (MultiNode l p)) :
    (multiPass leaves proof hl hp deepest nodes).nodes.map MultiNode.view =
      nodes.map MultiNode.view := by
  simpa [multiPass] using multiPassWorker_views leaves proof hl hp deepest nodes []

/-- This projection retains precisely the values readable by an even writer. -/
def MultiNode.oddView {l p : Nat} (node : MultiNode l p) :
    (NatOperand × Nat × Nat) × Option (MultiValue l p) :=
  (node.view, if node.isRight then some node.value else none)

theorem multiPassWorker_oddViews {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (deepest : Nat)
    (pending : List (MultiNode l p)) :
    ∀ doneRev, (multiPassWorker leaves proof hl hp deepest doneRev pending).nodes.map
      MultiNode.oddView = (doneRev.reverse ++ pending).map MultiNode.oddView := by
  induction pending with
  | nil => intro doneRev; simp only [multiPassWorker, List.append_nil]
  | cons node pending ih =>
      intro doneRev
      unfold multiPassWorker
      split
      · simpa [List.reverse_cons, List.append_assoc] using ih (node :: doneRev)
      · split
        · rfl
        · rename_i sibling found
          split
          · simpa [List.reverse_cons, List.append_assoc] using ih (node :: doneRev)
          · rename_i even
            change Indices.bit node.index node.shift ≠ true at even
            let updated : MultiNode l p := { node with
              value := (.hashed (rawCombine (node.value.bytes leaves proof hl hp)
                (sibling.value.bytes leaves proof hl hp))) }
            simpa [updated, MultiNode.oddView, MultiNode.view, MultiNode.isRight, even,
              List.reverse_cons, List.map_append, List.append_assoc] using
              ih (updated :: doneRev)

/-- Compaction writes at most one live output for each visited source slot. -/
theorem multiCompactWorker_length {l p : Nat} (deepest : Nat)
    (nodes : List (MultiNode l p)) : ∀ position written,
    (multiCompactWorker deepest position written nodes).active.length ≤ nodes.length := by
  induction nodes with
  | nil => intro position written; exact Nat.le_refl 0
  | cons node rest ih =>
      intro position written
      unfold multiCompactWorker
      split
      · exact Nat.le_trans (ih (position + 1) written) (Nat.le_succ _)
      · simpa using Nat.succ_le_succ (ih (position + 1) (written + 1))

@[simp] theorem multiInitialNodes_length (leaves proof : List Ssz.Bytes)
    (indices helpers : List NatOperand) (hl : leaves.length = indices.length)
    (hp : proof.length = helpers.length) :
    (multiInitialNodes leaves proof indices helpers hl hp).length =
      indices.length + helpers.length := by
  simp [multiInitialNodes]

@[simp] theorem multiInitEffects_length (pointer : Nat) (indices helpers : List NatOperand) :
    (multiInitEffects pointer indices helpers).length = indices.length + helpers.length := by
  simp [multiInitEffects]

/-- A failed typed reservation has neither a committed cursor nor an initializer. -/
theorem multiReserved_reservation_failure (leaves proof : List Ssz.Bytes)
    (indices helpers : List NatOperand) (hl : leaves.length = indices.length)
    (hp : proof.length = helpers.length) (layout : TypedArena.Layout)
    (arena : Delimited.ArenaState) (count : indices.length + helpers.length < 2^64)
    (failed : TypedArena.reserve layout arena.base arena.capacity arena.used
      (indices.length + helpers.length) = none) :
    multiReserved leaves proof indices helpers hl hp layout arena =
      ⟨.error .scratchExhausted, arena.used,
        [.reserve layout arena (indices.length + helpers.length) none]⟩ := by
  simp [multiReserved, count, failed]

/-- The count overflow branch never attempts the typed reservation. -/
theorem multiReserved_count_failure (leaves proof : List Ssz.Bytes)
    (indices helpers : List NatOperand) (hl : leaves.length = indices.length)
    (hp : proof.length = helpers.length) (layout : TypedArena.Layout)
    (arena : Delimited.ArenaState) (count : ¬ indices.length + helpers.length < 2^64) :
    multiReserved leaves proof indices helpers hl hp layout arena =
      unchanged arena.used (.error .scratchExhausted) := by
  simp [multiReserved, count]

/-- Even a failed fold retains the full reservation and every initialized slot. -/
theorem multiReserved_initialized (leaves proof : List Ssz.Bytes)
    (indices helpers : List NatOperand) (hl : leaves.length = indices.length)
    (hp : proof.length = helpers.length) (layout : TypedArena.Layout)
    (arena : Delimited.ArenaState) (allocated : Arena.Reservation)
    (count : indices.length + helpers.length < 2^64)
    (reserved : TypedArena.reserve layout arena.base arena.capacity arena.used
      (indices.length + helpers.length) = some allocated) :
    (multiReserved leaves proof indices helpers hl hp layout arena).used = allocated.used ∧
    (multiReserved leaves proof indices helpers hl hp layout arena).effects =
      .reserve layout arena (indices.length + helpers.length) (some allocated) ::
        multiInitEffects allocated.pointer indices helpers := by
  simp [multiReserved, count, reserved]

/-- Leaf-count failure occurs before the index helper algorithm is invoked. -/
theorem calculateMultiMerkleRoot_leaf_count (leaves proof : List Ssz.Bytes)
    (indices : List NatOperand) (layout : TypedArena.Layout) (arena : Delimited.ArenaState)
    (different : leaves.length ≠ indices.length) :
    calculateMultiMerkleRoot leaves proof indices layout arena =
      failCount .leafCount indices.length leaves.length arena := by
  simp [calculateMultiMerkleRoot, different]

/-- Erasure retains the original request-to-leaf pairing, and independently the
descending helper-to-proof pairing. It never sorts the claims or raw operands. -/
theorem multiInitialNodes_erase (leaves proof : List Ssz.Bytes)
    (indices helpers : List NatOperand) (hl : leaves.length = indices.length)
    (hp : proof.length = helpers.length) :
    (multiInitialNodes leaves proof indices helpers hl hp).map
      (MultiNode.erase leaves proof rfl rfl) =
      (indices.map NatOperand.value).zip leaves ++ (helpers.map NatOperand.value).zip proof := by
  unfold multiInitialNodes
  rw [List.map_append]
  congr 1
  · apply List.ext_getElem
    · simp [hl]
    · intro position leftBound rightBound
      simp [MultiNode.erase, MultiNode.position, MultiValue.bytes]
  · apply List.ext_getElem
    · simp [hp]
    · intro position leftBound rightBound
      simp [MultiNode.erase, MultiNode.position, MultiValue.bytes]

end SszNative.Proof

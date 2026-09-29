import SszHashStreamFinalize
import SszHashStreamUpdates

set_option autoImplicit false

namespace SszNative.HashStream

/-- Any finite sequence of updates refines hashing its actual concatenation.
The concatenation exists only in this specification, not in the native model. -/
theorem finalize_updates (chunks : List ByteArray) :
    finalize (updates new chunks) =
      Ssz.Sha256.hash ⟨(segmentBytes chunks).toArray⟩ := by
  apply finalize_eq_hash
  simpa using new_updates_represents chunks

/-- The caller may present a pre-existing concatenation instead; no restriction
is imposed on split points, empty inputs, or the total logical Nat length. -/
theorem finalize_updates_eq_hash (chunks : List ByteArray) (input : ByteArray)
    (sameBytes : segmentBytes chunks = input.data.toList) :
    finalize (updates new chunks) = Ssz.Sha256.hash input := by
  apply finalize_eq_hash
  rw [← sameBytes]
  exact new_updates_represents chunks

/-- Segmentation independence concerns the emitted digest, not the consumed
stale tails that differ between direct and buffered execution paths. -/
theorem finalize_segmentation (left right : List ByteArray)
    (sameBytes : segmentBytes left = segmentBytes right) :
    finalize (updates new left) = finalize (updates new right) := by
  have eqv := updates_segmentation left right sameBytes
  exact finalize_live_prefix _ _ eqv.1 eqv.2.2.2 eqv.2.2.1

/-- Both API compositions have checked update and finalization accesses and
emit precisely the pinned 32-byte digest. -/
theorem public_paths_safe (chunks : List ByteArray) :
    (updates new chunks).buffered.val < 64 ∧
    (∀ effect ∈ (finalizeRun (updates new chunks)).effects, effect.Safe) ∧
    (finalize (updates new chunks)).size = 32 := by
  exact ⟨buffered_bound _, finalize_effects_safe _, finalize_size _⟩

end SszNative.HashStream

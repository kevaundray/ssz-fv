import SszProofConstructionResources
import SszProofTraversalWidths

set_option autoImplicit false

namespace SszNative.Proof

/-- Even on failure, every completed initializer wrote one complete Hash, and
only a consecutive prefix of the already-reserved output has been initialized. -/
theorem fillHashRoots_complete_prefix (desc : Codec.Desc) (value : Codec.Value)
    (reservation : Arena.Reservation) (indices : List NatOperand) (position : Nat)
    (arena : Delimited.ArenaState) :
    ∃ completed, completed.length ≤ indices.length ∧
      (∀ root ∈ completed, root.size = 32) ∧
      hashWrites (fillHashRoots desc value reservation indices position arena).effects =
        initializedPrefix reservation.pointer position completed := by
  induction indices generalizing position arena with
  | nil => exact ⟨[], Nat.le_refl _, by simp, rfl⟩
  | cons index rest ih =>
      have noWrites := nodeRoot_hashWrites desc value index arena
      cases rooted : (nodeRoot desc value index arena).result with
      | error reason =>
          refine ⟨[], by simp, by simp, ?_⟩
          simpa only [fillHashRoots, bind, rooted, initializedPrefix] using noWrites
      | ok root =>
          obtain ⟨completed, bounded, widths, written⟩ := ih (position + 1)
            { arena with used := (nodeRoot desc value index arena).used }
          refine ⟨root :: completed,
            by simpa only [List.length_cons] using Nat.succ_le_succ bounded, ?_, ?_⟩
          · intro bytes member
            rcases List.mem_cons.mp member with same | member
            · subst bytes
              exact nodeRoot_size_raw desc value index arena root rooted
            · exact widths bytes member
          · cases filled : (fillHashRoots desc value reservation rest (position + 1)
                { arena with used := (nodeRoot desc value index arena).used }).result <;>
              simp only [fillHashRoots, bind, rooted, filled, unchanged, List.nil_append,
                List.append_nil, List.cons_append, hashWrites_append, noWrites, hashWrites,
                initializedPrefix, written]

theorem reserveHashRoots_slot_frame (count position : Nat) (arena : Delimited.ArenaState)
    (reservation : Arena.Reservation)
    (reserved : TypedArena.reserve hashLayout arena.base arena.capacity arena.used count =
      some reservation) (inside : position < count) :
    arena.base + arena.used ≤ reservation.pointer + 32 * position ∧
      reservation.pointer + 32 * position + 32 ≤ arena.base + reservation.used := by
  rcases reserveHashRoots_frame count arena reservation reserved with ⟨zero, _⟩ | ⟨_, pointer, used, _⟩
  · omega
  · rw [pointer, used]
    omega

end SszNative.Proof

import SszArm.MeasureOwnership
import SszArm.MeasureAllocationFacts

namespace SszArm.Measure

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value Outcome)
open Delimited (Span Protected MemoryFrame)

theorem Owned.allocation_protected {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value)
    (call : SszNative.NatArithmetic.Outcome NatOperand)
    (member : call ∈ (outcome s args desc value).calls)
    (reservation : SszNative.Arena.Reservation) (allocated : call.allocation = some reservation) :
    Protected (localWrites args (outcome s args desc value) ++ [(args.arena.toNat, 24)])
      reservation.pointer (8 * call.written.length) := by
  have bounds := (resource_measure (arenaOf s args) desc value).allocations call member reservation allocated
  have count := callsTwo_measure (arenaOf s args) desc value call member reservation allocated
  rcases owned.freeLocal with empty | separate
  · have unavailable : (arenaOf s args).capacity ≤ (arenaOf s args).used := by omega
    omega
  · right
    intro span inWrites
    have apart := separate span inWrites
    have available : (arenaOf s args).used ≤ (arenaOf s args).capacity := by omega
    omega

theorem bodyStack_saved (args : Args) (measured : Outcome NatOperand)
    (low : 288 ≤ args.stack.toNat) :
    Protected (bodyStackWrites args measured) (args.stack.toNat - 80) 80 := by
  right
  intro span member
  by_cases two : measured.calls.length = 2
  · simp only [bodyStackWrites, two, ↓reduceIte, List.mem_append, List.mem_singleton] at member
    rcases member with rfl | rfl <;> right <;> dsimp <;> omega
  · simp only [bodyStackWrites, two, ↓reduceIte, List.append_nil, List.mem_singleton] at member
    subst span
    right
    dsimp
    omega

/-- The actual allocations cannot overwrite prologue saves, even on an error
that retained earlier successful reservations. This is not an entry premise. -/
theorem saved_protected_body {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) :
    Protected (bodyWrites args (outcome s args desc value)) (args.stack.toNat - 80) 80 := by
  have saveMember : (args.stack.toNat - 80, 80) ∈ stackWrites args (outcome s args desc value) := by
    simp [stackWrites, saveWrites]
  have saveLocal : (args.stack.toNat - 80, 80) ∈ localWrites args (outcome s args desc value) := by
    exact List.mem_append.mpr (Or.inl saveMember)
  right
  intro span member
  simp only [bodyWrites, List.mem_append] at member
  rcases member with (lowering | result) | allocation
  · rcases bodyStack_saved args (outcome s args desc value) owned.stackLow with empty | separate
    · exact False.elim ((by decide : (80 : Nat) ≠ 0) empty)
    · exact separate span lowering
  · rcases owned.resultStack span result with empty | separate
    · have nonempty : span.2 ≠ 0 := by
        cases measured : (outcome s args desc value).result with
        | ok operand =>
          simp only [resultWrites, measured, List.mem_cons, List.not_mem_nil, or_false] at result
          rcases result with rfl | rfl
          · change (40 : Nat) ≠ 0
            decide
          · change (4 : Nat) ≠ 0
            decide
        | error reason =>
          simp only [resultWrites, measured, List.mem_singleton] at result
          subst span
          unfold resultExtent
          split
          · change (72 : Nat) ≠ 0
            decide
          · change (68 : Nat) ≠ 0
            decide
      exact False.elim (nonempty empty)
    · have apart := separate _ saveMember
      exact apart.symm
  · simp only [allocationWrites, List.mem_flatMap] at allocation
    obtain ⟨call, callMember, spanMember⟩ := allocation
    cases allocated : call.allocation with
    | none => simp only [allocated, List.not_mem_nil] at spanMember
    | some reservation =>
      simp only [allocated, List.mem_cons, List.not_mem_nil, or_false] at spanMember
      rcases spanMember with rfl | rfl
      · rcases owned.headerLocal with empty | separate
        · contradiction
        · have apart := separate _ saveLocal
          dsimp at apart ⊢
          omega
      · rcases owned.allocation_protected call callMember reservation allocated with empty | separate
        · have count := callsTwo_measure (arenaOf s args) desc value call callMember reservation allocated
          omega
        · have apart := separate _ (List.mem_append.mpr (Or.inl saveLocal))
          exact apart.symm

end SszArm.Measure

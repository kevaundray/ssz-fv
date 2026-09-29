import SszCodecMeasure

set_option autoImplicit false

namespace SszNative.CodecMeasure

open Codec (Desc Value Error)

/-- Binding preserves a failed call's complete cursor and trace. In particular,
there is no transaction boundary around a child, parts traversal, or union. -/
theorem bind_failure {α β : Type} (first : Outcome α) (next : α → Nat → Outcome β)
    (reason : Error) (failed : first.result = .error reason) :
    bind first next = ⟨.error reason, first.used, first.effects⟩ := by
  simp only [bind, failed]

/-- A successful call commits before its successor runs, and traces concatenate
in execution order rather than retaining successful calls only. -/
theorem bind_success {α β : Type} (first : Outcome α) (next : α → Nat → Outcome β)
    (value : α) (success : first.result = .ok value) :
    bind first next =
      ⟨(next value first.used).result, (next value first.used).used,
        first.effects ++ (next value first.used).effects⟩ := by
  simp only [bind, success]

theorem reservePlans_zero (arena : Delimited.ArenaState) :
    reservePlans 0 arena =
      ⟨.ok ⟨8, arena.used⟩, arena.used,
        [.reservePlans 0 arena (some ⟨8, arena.used⟩)]⟩ := by
  simp only [reservePlans, Nat.mul_zero, Arena.reserve, ↓reduceIte]

/-- The preallocation failure happens before any callback; no initializer is
invoked, but the failed plan reservation remains an observable attempted effect. -/
theorem measureParts_reservation_failure (parts : Parts) (values : List Value)
    (visit : Visit values) (arena : Delimited.ArenaState) (retain : Bool)
    (keep : (retain && !parts.allFixed) = true)
    (failed : Arena.reserve arena.base arena.capacity arena.used
      (5 * parts.paired values) = none) :
    measureParts parts values visit arena retain =
      ⟨.error (.primitive (.arithmetic .scratchExhausted)), arena.used,
        [.reservePlans (parts.paired values) arena none]⟩ := by
  simp only [measureParts, keep, ↓reduceIte, reservePlans, failed, bind]

/-- Once the paired prefix has been visited, fields arity wins over the final
arithmetic, offset check, and host conversion, preserving the prefix cursor. -/
theorem finishParts_arity_failure (parts : Parts) (values : List Value)
    (totals : Partial) (allocation : Option Arena.Reservation)
    (arena : Delimited.ArenaState) (mismatch : parts.arity values = false) :
    finishParts parts values totals allocation arena =
      unchanged arena.used (.error (.primitive .wrongType)) := by
  simp only [finishParts, mismatch, Bool.false_eq_true, ↓reduceIte]

/-- Every committed plan slot occupies its exact native64 stride. This equation
includes the child payload, not merely a count of writes. -/
theorem writePlan_slot (reservation : Arena.Reservation) (index : Nat)
    (plan : Plan) (used : Nat) :
    writePlan (some reservation) index plan used =
      ⟨.ok (), used, [.writePlan (reservation.pointer + 40 * index) index plan]⟩ := rfl

/-- A duplicate selector after the first numerical match is not inspected. -/
theorem option_first (chosen selector : NatOperand) (desc : Desc)
    (rest : List (NatOperand × Desc)) (same : chosen.value = selector.value) :
    option ((chosen, desc) :: rest) selector = .ok desc := by
  simp only [option, same, ↓reduceIte]

theorem option_skip (chosen selector : NatOperand) (desc : Desc)
    (rest : List (NatOperand × Desc)) (different : chosen.value ≠ selector.value) :
    option ((chosen, desc) :: rest) selector = option rest selector := by
  simp only [option, different, ↓reduceIte]

/-- Distinct successful initializer slots cannot overlap, independently of what
padding bytes the native store happens to write. -/
theorem plan_slots_disjoint (pointer left right byte : Nat) (ordered : left < right)
    (inside : PlanWriteSpan (pointer + 40 * left) byte) :
    ¬ PlanWriteSpan (pointer + 40 * right) byte := by
  unfold PlanWriteSpan at *
  omega

/-- Every permitted byte of an initialized slot belongs to the already reserved
payload, which lies in caller storage. Nested child allocations begin after this
payload and therefore cannot make a slot extend the reservation retroactively. -/
theorem plan_slot_inside_reservation (arena : Delimited.ArenaState) (count index byte : Nat)
    (valid : Arena.Valid arena.base arena.capacity arena.used)
    (reservation : Arena.Reservation)
    (reserved : Arena.reserve arena.base arena.capacity arena.used (5 * count) = some reservation)
    (indexBound : index < count)
    (inside : PlanWriteSpan (reservation.pointer + 40 * index) byte) :
    reservation.pointer ≤ byte ∧ byte < arena.base + reservation.used ∧
      byte < arena.base + arena.capacity := by
  have properties := Arena.success_properties arena.base arena.capacity arena.used
    (5 * count) valid (by omega) reservation reserved
  unfold PlanWriteSpan at inside
  rcases properties with ⟨_, _, _, _, _, _, payload, storage, _⟩
  omega

end SszNative.CodecMeasure

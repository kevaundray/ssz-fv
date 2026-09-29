import SszCodecEmit
import SszCodecMeasureResources

set_option autoImplicit false

namespace SszNative.CodecEmit

open Codec (Desc Value Error)
open CodecMeasure (Plan)

/-- Caller-output emission commits precisely the retained measurement resources,
including when measurement, host narrowing, capacity, or private emission fails. -/
theorem serialize_resources (desc : Desc) (value : Value) (capacity : Nat)
    (arena : Delimited.ArenaState) :
    (serialize desc value capacity arena).used = (CodecMeasure.measure desc value arena true).used ∧
    (serialize desc value capacity arena).effects = (CodecMeasure.measure desc value arena true).effects := by
  cases measured : (CodecMeasure.measure desc value arena true).result with
  | error reason => simp only [serialize, measured]; exact ⟨True.intro, True.intro⟩
  | ok plan =>
    cases host : (CodecMeasure.hostSize plan.size
        (CodecMeasure.measure desc value arena true).used).result with
    | error reason => simp only [serialize, measured, host]; exact ⟨True.intro, True.intro⟩
    | ok size =>
      by_cases fits : size ≤ capacity <;>
        simp only [serialize, measured, host, fits, ↓reduceIte] <;> exact ⟨True.intro, True.intro⟩

theorem serialize_measure_error (desc : Desc) (value : Value) (capacity : Nat)
    (arena : Delimited.ArenaState) (reason : Error)
    (measured : (CodecMeasure.measure desc value arena true).result = .error reason) :
    serialize desc value capacity arena =
      ⟨.error (.returned reason), (CodecMeasure.measure desc value arena true).used,
        (CodecMeasure.measure desc value arena true).effects, []⟩ := by
  simp only [serialize, measured]

theorem serialize_host_error (desc : Desc) (value : Value) (capacity : Nat)
    (arena : Delimited.ArenaState) (plan : Plan) (reason : Error)
    (measured : (CodecMeasure.measure desc value arena true).result = .ok plan)
    (host : (CodecMeasure.hostSize plan.size (CodecMeasure.measure desc value arena true).used).result = .error reason) :
    serialize desc value capacity arena =
      ⟨.error (.returned reason), (CodecMeasure.measure desc value arena true).used,
        (CodecMeasure.measure desc value arena true).effects, []⟩ := by
  simp only [serialize, measured, host]

theorem serialize_capacity_error (desc : Desc) (value : Value) (capacity : Nat)
    (arena : Delimited.ArenaState) (plan : Plan) (size : Nat)
    (measured : (CodecMeasure.measure desc value arena true).result = .ok plan)
    (host : (CodecMeasure.hostSize plan.size (CodecMeasure.measure desc value arena true).used).result = .ok size)
    (small : ¬ size ≤ capacity) :
    serialize desc value capacity arena =
      ⟨.error (.returned (.primitive .outputTooSmall)),
        (CodecMeasure.measure desc value arena true).used,
        (CodecMeasure.measure desc value arena true).effects, []⟩ := by
  simp only [serialize, measured, host, small, ↓reduceIte]

/-- The emitter receives the measured prefix, not the caller's full capacity. -/
theorem serialize_emit_order (desc : Desc) (value : Value) (capacity : Nat)
    (arena : Delimited.ArenaState) (plan : Plan) (size : Nat)
    (measured : (CodecMeasure.measure desc value arena true).result = .ok plan)
    (host : (CodecMeasure.hostSize plan.size (CodecMeasure.measure desc value arena true).used).result = .ok size)
    (fits : size ≤ capacity) :
    serialize desc value capacity arena =
      ⟨(emit desc value (some plan) ⟨0, size⟩).result,
        (CodecMeasure.measure desc value arena true).used,
        (CodecMeasure.measure desc value arena true).effects,
        (emit desc value (some plan) ⟨0, size⟩).writes⟩ := by
  simp only [serialize, measured, host, fits, ↓reduceIte]

theorem serialize_cursorSafe (desc : Desc) (value : Value) (capacity : Nat)
    (arena : Delimited.ArenaState) :
    CodecMeasure.CursorSafe arena (serialize desc value capacity arena).used := by
  rw [(serialize_resources desc value capacity arena).1]
  exact CodecMeasure.measure_cursorSafe desc value arena true

theorem serialize_valid (desc : Desc) (value : Value) (capacity : Nat)
    (arena : Delimited.ArenaState) (valid : Arena.Valid arena.base arena.capacity arena.used) :
    Arena.Valid arena.base arena.capacity (serialize desc value capacity arena).used :=
  (serialize_cursorSafe desc value capacity arena).2 valid

theorem serializeAlloc_measure_error (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (reason : Error)
    (measured : (CodecMeasure.measure desc value arena true).result = .error reason) :
    serializeAlloc desc value arena =
      ⟨⟨.error (.returned reason), (CodecMeasure.measure desc value arena true).used,
        (CodecMeasure.measure desc value arena true).effects, []⟩, none⟩ := by
  simp only [serializeAlloc, measured]

theorem serializeAlloc_host_error (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (plan : Plan) (reason : Error)
    (measured : (CodecMeasure.measure desc value arena true).result = .ok plan)
    (host : (CodecMeasure.hostSize plan.size (CodecMeasure.measure desc value arena true).used).result = .error reason) :
    serializeAlloc desc value arena =
      ⟨⟨.error (.returned reason), (CodecMeasure.measure desc value arena true).used,
        (CodecMeasure.measure desc value arena true).effects, []⟩, none⟩ := by
  simp only [serializeAlloc, measured, host]

/-- A failed final reservation records the attempt but makes no output write
and does not roll back or extend the measurement cursor or effects. -/
theorem serializeAlloc_reserve_error (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (plan : Plan) (size : Nat)
    (measured : (CodecMeasure.measure desc value arena true).result = .ok plan)
    (host : (CodecMeasure.hostSize plan.size (CodecMeasure.measure desc value arena true).used).result = .ok size)
    (reserved : Arena.reserveBytes arena.base arena.capacity
      (CodecMeasure.measure desc value arena true).used size = none) :
    serializeAlloc desc value arena =
      ⟨⟨.error (.returned (.primitive (.arithmetic .scratchExhausted))),
        (CodecMeasure.measure desc value arena true).used,
        (CodecMeasure.measure desc value arena true).effects, []⟩, some (size, none)⟩ := by
  simp only [serializeAlloc, measured, host, reserved]

theorem serializeAlloc_emit_order (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (plan : Plan) (size : Nat) (reservation : Arena.Reservation)
    (measured : (CodecMeasure.measure desc value arena true).result = .ok plan)
    (host : (CodecMeasure.hostSize plan.size (CodecMeasure.measure desc value arena true).used).result = .ok size)
    (reserved : Arena.reserveBytes arena.base arena.capacity
      (CodecMeasure.measure desc value arena true).used size = some reservation) :
    serializeAlloc desc value arena =
      ⟨⟨(emit desc value (some plan) ⟨reservation.pointer, size⟩).result,
        reservation.used, (CodecMeasure.measure desc value arena true).effects,
        (emit desc value (some plan) ⟨reservation.pointer, size⟩).writes⟩,
        some (size, some reservation)⟩ := by
  simp only [serializeAlloc, measured, host, reserved]

/-- Zero-sized final allocations use pointer one and leave the measured cursor
unchanged; they still invoke emission and record a successful allocation. -/
theorem serializeAlloc_zero (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (plan : Plan)
    (measured : (CodecMeasure.measure desc value arena true).result = .ok plan)
    (host : (CodecMeasure.hostSize plan.size (CodecMeasure.measure desc value arena true).used).result = .ok 0) :
    serializeAlloc desc value arena =
      ⟨⟨(emit desc value (some plan) ⟨1, 0⟩).result,
        (CodecMeasure.measure desc value arena true).used,
        (CodecMeasure.measure desc value arena true).effects,
        (emit desc value (some plan) ⟨1, 0⟩).writes⟩,
        some (0, some ⟨1, (CodecMeasure.measure desc value arena true).used⟩)⟩ := by
  exact serializeAlloc_emit_order desc value arena plan 0 _ measured host
    (Arena.reserveBytes_zero _ _ _)

/-- The separate reservation field records exactly the final byte-allocation
attempt, after both retained measurement and host narrowing have succeeded. -/
theorem serializeAlloc_reservation_order (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) :
    (serializeAlloc desc value arena).reservation =
      match (CodecMeasure.measure desc value arena true).result with
      | .error _ => none
      | .ok plan =>
        match (CodecMeasure.hostSize plan.size (CodecMeasure.measure desc value arena true).used).result with
        | .error _ => none
        | .ok size => some (size, Arena.reserveBytes arena.base arena.capacity
            (CodecMeasure.measure desc value arena true).used size) := by
  cases measured : (CodecMeasure.measure desc value arena true).result with
  | error reason => simp only [serializeAlloc, measured]
  | ok plan =>
    cases host : (CodecMeasure.hostSize plan.size
        (CodecMeasure.measure desc value arena true).used).result with
    | error reason => simp only [serializeAlloc, measured, host]
    | ok size =>
      cases reserved : Arena.reserveBytes arena.base arena.capacity
          (CodecMeasure.measure desc value arena true).used size <;>
        simp only [serializeAlloc, measured, host, reserved]

/-- The final cursor is the measured cursor unless the actual final byte
reservation succeeds. This equation does not inspect the emitter's result. -/
theorem serializeAlloc_used_order (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) :
    (serializeAlloc desc value arena).written.used =
      match (serializeAlloc desc value arena).reservation with
      | some (_, some reservation) => reservation.used
      | _ => (CodecMeasure.measure desc value arena true).used := by
  cases measured : (CodecMeasure.measure desc value arena true).result with
  | error reason => simp only [serializeAlloc, measured]
  | ok plan =>
    cases host : (CodecMeasure.hostSize plan.size
        (CodecMeasure.measure desc value arena true).used).result with
    | error reason => simp only [serializeAlloc, measured, host]
    | ok size =>
      cases reserved : Arena.reserveBytes arena.base arena.capacity
          (CodecMeasure.measure desc value arena true).used size <;>
        simp only [serializeAlloc, measured, host, reserved]

private theorem reserveBytes_cursorSafe (arena : Delimited.ArenaState) (size : Nat)
    (reservation : Arena.Reservation)
    (reserved : Arena.reserveBytes arena.base arena.capacity arena.used size = some reservation) :
    CodecMeasure.CursorSafe arena reservation.used := by
  refine ⟨?_, fun valid => Arena.reserveBytes_valid _ _ _ _ valid reservation reserved⟩
  by_cases zero : size = 0
  · subst size
    have same : (⟨1, arena.used⟩ : Arena.Reservation) = reservation := by
      simpa only [Arena.reserveBytes_zero, Option.some.injEq] using reserved
    subst reservation
    exact Nat.le_refl _
  · have shape := (Arena.reserveBytes_some_iff _ _ _ _ (by omega) reservation).1 reserved
    rw [shape.2]
    exact Nat.le_add_right _ _

/-- Unconditional resource safety: no future emitter-success premise, physical
input hypothesis, or generated-plan oracle is required. -/
theorem serializeAlloc_resources (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) :
    (serializeAlloc desc value arena).written.effects =
      (CodecMeasure.measure desc value arena true).effects ∧
    CodecMeasure.CursorSafe arena (serializeAlloc desc value arena).written.used := by
  have measuredSafe := CodecMeasure.measure_cursorSafe desc value arena true
  cases measured : (CodecMeasure.measure desc value arena true).result with
  | error reason =>
    simp only [serializeAlloc, measured]
    exact ⟨True.intro, measuredSafe⟩
  | ok plan =>
    cases host : (CodecMeasure.hostSize plan.size
        (CodecMeasure.measure desc value arena true).used).result with
    | error reason =>
      simp only [serializeAlloc, measured, host]
      exact ⟨True.intro, measuredSafe⟩
    | ok size =>
      cases reserved : Arena.reserveBytes arena.base arena.capacity
          (CodecMeasure.measure desc value arena true).used size with
      | none =>
        simp only [serializeAlloc, measured, host, reserved]
        exact ⟨True.intro, measuredSafe⟩
      | some reservation =>
        simp only [serializeAlloc, measured, host, reserved]
        exact ⟨True.intro, CodecMeasure.cursorSafe_trans arena _ _ measuredSafe
          (reserveBytes_cursorSafe { arena with used := (CodecMeasure.measure desc value arena true).used }
            size reservation reserved)⟩

theorem serializeAlloc_valid (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (valid : Arena.Valid arena.base arena.capacity arena.used) :
    Arena.Valid arena.base arena.capacity (serializeAlloc desc value arena).written.used :=
  (serializeAlloc_resources desc value arena).2.2 valid

/-- A recorded successful attempt is the real byte allocator's result, even
when the subsequent private emission reports a fault. -/
theorem serializeAlloc_reserved (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (size : Nat) (reservation : Arena.Reservation)
    (observed : (serializeAlloc desc value arena).reservation = some (size, some reservation)) :
    Arena.reserveBytes arena.base arena.capacity
      (CodecMeasure.measure desc value arena true).used size = some reservation := by
  rw [serializeAlloc_reservation_order] at observed
  split at observed
  · cases observed
  · split at observed
    · cases observed
    · have same := Option.some.inj observed
      have sizes := congrArg Prod.fst same
      have allocations := congrArg Prod.snd same
      dsimp only at sizes allocations
      subst size
      exact allocations

/-- Positive final byte storage lies inside the arena and strictly after the
entire already-used prefix, including every retained measurement allocation. -/
theorem serializeAlloc_interval (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (size : Nat) (reservation : Arena.Reservation)
    (valid : Arena.Valid arena.base arena.capacity arena.used) (positive : 0 < size)
    (observed : (serializeAlloc desc value arena).reservation = some (size, some reservation)) :
    reservation.pointer = arena.base + (CodecMeasure.measure desc value arena true).used ∧
    reservation.used = (CodecMeasure.measure desc value arena true).used + size ∧
    (CodecMeasure.measure desc value arena true).used < reservation.used ∧
    reservation.used ≤ arena.capacity ∧ 0 < reservation.pointer ∧
    reservation.pointer + size ≤ arena.base + arena.capacity ∧
    (∀ address, arena.base ≤ address →
      address < arena.base + (CodecMeasure.measure desc value arena true).used →
      ¬ (reservation.pointer ≤ address ∧ address < reservation.pointer + size)) := by
  have interval := Arena.reserveBytes_interval arena.base arena.capacity
    (CodecMeasure.measure desc value arena true).used size
    (CodecMeasure.measure_valid desc value arena true valid) positive reservation
    (serializeAlloc_reserved desc value arena size reservation observed)
  refine ⟨interval.1, interval.2.1, interval.2.2.1, interval.2.2.2.1,
    interval.2.2.2.2.1, interval.2.2.2.2.2, ?_⟩
  intro address lower upper overlap
  rw [interval.1] at overlap
  omega

end SszNative.CodecEmit

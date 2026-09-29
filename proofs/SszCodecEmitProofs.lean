import SszCodecEmitSafety
import SszCodecEmitSemantic
import SszCodecEmitResources
import SszCodecEmitOrder

set_option autoImplicit false

namespace SszNative.CodecEmit

open Codec (Desc Value Error)
open CodecMeasure (Plan)

/-- Public refinement has no private-fault alternative. Its only host deviations
are actual returned scratch exhaustion and actual returned output shortage. -/
def Refines (result : Except Fault Nat) (expected : Except Ssz.Err Nat) : Prop :=
  ∃ native : Except Error Nat,
    result = native.mapError Fault.returned ∧ CodecMeasure.Refines id native expected

theorem Refines.returned {result : Except Fault Nat} {expected : Except Ssz.Err Nat}
    (correct : Refines result expected) (reason : Error)
    (failed : result = .error (.returned reason)) :
    CodecMeasure.Refines id (.error reason) expected := by
  obtain ⟨native, same, refined⟩ := correct
  cases native with
  | ok size =>
    simp only [Except.mapError, failed] at same
    cases same
  | error actual =>
    have identical : reason = actual := by
      simpa only [Except.mapError, failed, Except.error.injEq, Fault.returned.injEq] using same
    subst actual
    exact refined

theorem Refines.no_badRepresentation {result : Except Fault Nat}
    {expected : Except Ssz.Err Nat} (correct : Refines result expected) :
    result ≠ .error (.returned (.primitive (.arithmetic .badRepresentation))) := by
  intro failed
  have refined := correct.returned _ failed
  simp [CodecMeasure.Refines, Codec.eraseResult, Serialize.eraseResult] at refined

theorem Refines.no_private {result : Except Fault Nat} {expected : Except Ssz.Err Nat}
    (correct : Refines result expected) :
    result ≠ .error .fieldIndex ∧
      ∀ available start count, result ≠ .error (.bounds available start count) := by
  obtain ⟨native, same, _⟩ := correct
  rw [same]
  cases native <;> simp [Except.mapError]

theorem host_success (size : NatOperand) (used result : Nat)
    (success : (CodecMeasure.hostSize size used).result = .ok result) :
    result = size.value ∧ size.value < 2 ^ 64 := by
  unfold CodecMeasure.hostSize Serialize.hostSize at success
  split at success
  next fits =>
    have same : size.value = result := by
      simpa only [Serialize.unchanged, Except.mapError, Except.ok.injEq] using success
    exact ⟨same.symm, fits⟩
  next fits =>
    simp only [Serialize.unchanged, Except.mapError] at success
    cases success

theorem host_failure (size : NatOperand) (used : Nat) (reason : Error)
    (failure : (CodecMeasure.hostSize size used).result = .error reason) :
    reason = .primitive .outputTooSmall := by
  unfold CodecMeasure.hostSize Serialize.hostSize at failure
  split at failure
  · simp only [Serialize.unchanged, Except.mapError] at failure
    cases failure
  · simpa only [Serialize.unchanged, Except.mapError, Except.error.injEq] using failure.symm

/-- Both safety and byte refinement are discharged from the original physical
input and the observed successful measurement, not assumed of a future emit. -/
theorem measured_emits (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (physical : value.Physical) (plan : Plan) (size address : Nat)
    (measured : (CodecMeasure.measure desc value arena true).result = .ok plan)
    (converted : (CodecMeasure.hostSize plan.size
      (CodecMeasure.measure desc value arena true).used).result = .ok size) :
    (emit desc value (some plan) ⟨address, size⟩).result = .ok size ∧
      ∃ bytes, Ssz.serialize desc.erase value.erase = .ok bytes ∧ bytes.size = size ∧
        Encodes (emit desc value (some plan) ⟨address, size⟩).writes address bytes := by
  obtain ⟨rfl, host⟩ := host_success plan.size _ size converted
  have generated := measure_generated desc value arena true physical plan measured
  have safe := generated_emit_success desc value true plan (some plan)
    ⟨address, plan.size.value⟩ generated (Or.inl rfl) rfl (fun _ => rfl) (Nat.le_refl _) host
  refine ⟨safe, ?_⟩
  have correct := CodecMeasure.measure_success desc value arena true physical plan measured
  cases semantic : Ssz.serialize desc.erase value.erase with
  | error reason =>
    simp only [semantic, Except.map] at correct
    cases correct
  | ok bytes =>
    have width : bytes.size = plan.size.value := by
      simpa only [semantic, Except.map, Except.ok.injEq] using correct
    refine ⟨bytes, rfl, width, ?_⟩
    exact generated_emit_encodes desc value true plan (some plan)
      ⟨address, plan.size.value⟩ bytes generated (Or.inl rfl) rfl (fun _ => rfl)
      (Nat.le_refl _) host semantic

private theorem refines_output (expected : Except Ssz.Err Nat) :
    Refines (.error (.returned (.primitive .outputTooSmall))) expected :=
  ⟨.error (.primitive .outputTooSmall), rfl, Or.inr (Or.inr rfl)⟩

private theorem refines_scratch (expected : Except Ssz.Err Nat) :
    Refines (.error (.returned (.primitive (.arithmetic .scratchExhausted)))) expected :=
  ⟨.error (.primitive (.arithmetic .scratchExhausted)), rfl, Or.inr (Or.inl rfl)⟩

/-- All physical values and all declarations, including semantic rejection.
The public result cannot contain BadRepresentation or a private bounds fault. -/
theorem serialize_refines (desc : Desc) (value : Value) (capacity : Nat)
    (arena : Delimited.ArenaState) (physical : value.Physical) :
    Refines (serialize desc value capacity arena).result
      ((Ssz.serialize desc.erase value.erase).map Array.size) := by
  have correct := CodecMeasure.measure_refines desc value arena true physical
  cases measured : (CodecMeasure.measure desc value arena true).result with
  | error reason =>
    refine ⟨.error reason, ?_, ?_⟩
    · simp only [serialize, measured, Except.mapError]
    · simpa only [CodecMeasure.Refines, measured, Except.map, Except.error.injEq] using correct
  | ok plan =>
    cases converted : (CodecMeasure.hostSize plan.size
        (CodecMeasure.measure desc value arena true).used).result with
    | error reason =>
      have same := host_failure plan.size _ reason converted
      subst reason
      simpa only [serialize, measured, converted] using
        refines_output ((Ssz.serialize desc.erase value.erase).map Array.size)
    | ok size =>
      by_cases fits : size ≤ capacity
      · obtain ⟨emitted, bytes, semantic, width, _⟩ :=
          measured_emits desc value arena physical plan size 0 measured converted
        refine ⟨.ok size, ?_, Or.inl ?_⟩
        · simp only [serialize, measured, converted, fits, ↓reduceIte, emitted, Except.mapError]
        · simp only [Except.map, Codec.eraseResult, id_eq, semantic, width]
      · simpa only [serialize, measured, converted, fits, ↓reduceIte] using
          refines_output ((Ssz.serialize desc.erase value.erase).map Array.size)

theorem serialize_success (desc : Desc) (value : Value) (capacity : Nat)
    (arena : Delimited.ArenaState) (physical : value.Physical) (size : Nat)
    (success : (serialize desc value capacity arena).result = .ok size) :
    ∃ bytes, Ssz.serialize desc.erase value.erase = .ok bytes ∧ bytes.size = size ∧
      size ≤ capacity ∧ Encodes (serialize desc value capacity arena).writes 0 bytes := by
  cases measured : (CodecMeasure.measure desc value arena true).result with
  | error reason => simp only [serialize, measured] at success; cases success
  | ok plan =>
    cases converted : (CodecMeasure.hostSize plan.size
        (CodecMeasure.measure desc value arena true).used).result with
    | error reason => simp only [serialize, measured, converted] at success; cases success
    | ok actual =>
      by_cases fits : actual ≤ capacity
      · obtain ⟨emitted, bytes, semantic, width, encoded⟩ :=
          measured_emits desc value arena physical plan actual 0 measured converted
        have same : actual = size := by
          simpa only [serialize, measured, converted, fits, ↓reduceIte,
            emitted, Except.ok.injEq] using success
        subst size
        refine ⟨bytes, semantic, width, fits, ?_⟩
        simpa only [serialize, measured, converted, fits, ↓reduceIte] using encoded
      · simp only [serialize, measured, converted, fits, ↓reduceIte] at success
        cases success

theorem serialize_failure_writes (desc : Desc) (value : Value) (capacity : Nat)
    (arena : Delimited.ArenaState) (physical : value.Physical) (reason : Fault)
    (failure : (serialize desc value capacity arena).result = .error reason) :
    (serialize desc value capacity arena).writes = [] := by
  cases measured : (CodecMeasure.measure desc value arena true).result with
  | error reason => simp only [serialize, measured]
  | ok plan =>
    cases converted : (CodecMeasure.hostSize plan.size
        (CodecMeasure.measure desc value arena true).used).result with
    | error reason => simp only [serialize, measured, converted]
    | ok size =>
      by_cases fits : size ≤ capacity
      · have emitted := (measured_emits desc value arena physical plan size 0 measured converted).1
        simp only [serialize, measured, converted, fits, ↓reduceIte, emitted] at failure
        cases failure
      · simp only [serialize, measured, converted, fits, ↓reduceIte]

theorem serialize_failure_unchanged (desc : Desc) (value : Value) (capacity : Nat)
    (arena : Delimited.ArenaState) (physical : value.Physical) (reason : Fault)
    (failure : (serialize desc value capacity arena).result = .error reason)
    (before : Nat → Option UInt8) :
    applyWrites before (serialize desc value capacity arena).writes = before := by
  rw [serialize_failure_writes desc value capacity arena physical reason failure]
  rfl

/-- Success initializes exactly the returned prefix even in initially
uninitialized memory, and never depends on any old output byte. -/
theorem serialize_output (desc : Desc) (value : Value) (capacity : Nat)
    (arena : Delimited.ArenaState) (physical : value.Physical) (size : Nat)
    (success : (serialize desc value capacity arena).result = .ok size) :
    ∃ bytes, Ssz.serialize desc.erase value.erase = .ok bytes ∧ bytes.size = size ∧
      size ≤ capacity ∧
      (∀ before index, (inside : index < bytes.size) →
        applyWrites before (serialize desc value capacity arena).writes index = some bytes[index]) ∧
      (∀ before index, size ≤ index →
        applyWrites before (serialize desc value capacity arena).writes index = before index) := by
  obtain ⟨bytes, semantic, width, fits, encoded⟩ :=
    serialize_success desc value capacity arena physical size success
  refine ⟨bytes, semantic, width, fits, ?_, ?_⟩
  · intro before index inside
    simpa only [Nat.zero_add] using encoded.initialized before index inside
  · intro before index outside
    apply encoded.frame before index
    exact Or.inr (by omega)

theorem serializeAlloc_refines (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (physical : value.Physical) :
    Refines (serializeAlloc desc value arena).written.result
      ((Ssz.serialize desc.erase value.erase).map Array.size) := by
  have correct := CodecMeasure.measure_refines desc value arena true physical
  cases measured : (CodecMeasure.measure desc value arena true).result with
  | error reason =>
    refine ⟨.error reason, ?_, ?_⟩
    · simp only [serializeAlloc, measured, Except.mapError]
    · simpa only [CodecMeasure.Refines, measured, Except.map, Except.error.injEq] using correct
  | ok plan =>
    cases converted : (CodecMeasure.hostSize plan.size
        (CodecMeasure.measure desc value arena true).used).result with
    | error reason =>
      have same := host_failure plan.size _ reason converted
      subst reason
      simpa only [serializeAlloc, measured, converted] using
        refines_output ((Ssz.serialize desc.erase value.erase).map Array.size)
    | ok size =>
      cases reserved : Arena.reserveBytes arena.base arena.capacity
          (CodecMeasure.measure desc value arena true).used size with
      | none =>
        simpa only [serializeAlloc, measured, converted, reserved] using
          refines_scratch ((Ssz.serialize desc.erase value.erase).map Array.size)
      | some reservation =>
        obtain ⟨emitted, bytes, semantic, width, _⟩ :=
          measured_emits desc value arena physical plan size reservation.pointer measured converted
        refine ⟨.ok size, ?_, Or.inl ?_⟩
        · simp only [serializeAlloc, measured, converted, reserved, emitted, Except.mapError]
        · simp only [Except.map, Codec.eraseResult, id_eq, semantic, width]

theorem serializeAlloc_success (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (physical : value.Physical) (size : Nat)
    (success : (serializeAlloc desc value arena).written.result = .ok size) :
    ∃ bytes reservation, Ssz.serialize desc.erase value.erase = .ok bytes ∧ bytes.size = size ∧
      (serializeAlloc desc value arena).reservation = some (size, some reservation) ∧
      Arena.reserveBytes arena.base arena.capacity (CodecMeasure.measure desc value arena true).used
        size = some reservation ∧
      (serializeAlloc desc value arena).written.used = reservation.used ∧
      Encodes (serializeAlloc desc value arena).written.writes reservation.pointer bytes := by
  cases measured : (CodecMeasure.measure desc value arena true).result with
  | error reason => simp only [serializeAlloc, measured] at success; cases success
  | ok plan =>
    cases converted : (CodecMeasure.hostSize plan.size
        (CodecMeasure.measure desc value arena true).used).result with
    | error reason => simp only [serializeAlloc, measured, converted] at success; cases success
    | ok actual =>
      cases reserved : Arena.reserveBytes arena.base arena.capacity
          (CodecMeasure.measure desc value arena true).used actual with
      | none => simp only [serializeAlloc, measured, converted, reserved] at success; cases success
      | some reservation =>
        obtain ⟨emitted, bytes, semantic, width, encoded⟩ :=
          measured_emits desc value arena physical plan actual reservation.pointer measured converted
        have same : actual = size := by
          simpa only [serializeAlloc, measured, converted, reserved, emitted,
            Except.ok.injEq] using success
        subst size
        refine ⟨bytes, reservation, semantic, width, ?_, reserved, ?_, ?_⟩
        · simp only [serializeAlloc, measured, converted, reserved]
        · simp only [serializeAlloc, measured, converted, reserved]
        · simpa only [serializeAlloc, measured, converted, reserved] using encoded

theorem serializeAlloc_failure_writes (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (physical : value.Physical) (reason : Fault)
    (failure : (serializeAlloc desc value arena).written.result = .error reason) :
    (serializeAlloc desc value arena).written.writes = [] := by
  cases measured : (CodecMeasure.measure desc value arena true).result with
  | error reason => simp only [serializeAlloc, measured]
  | ok plan =>
    cases converted : (CodecMeasure.hostSize plan.size
        (CodecMeasure.measure desc value arena true).used).result with
    | error reason => simp only [serializeAlloc, measured, converted]
    | ok size =>
      cases reserved : Arena.reserveBytes arena.base arena.capacity
          (CodecMeasure.measure desc value arena true).used size with
      | none => simp only [serializeAlloc, measured, converted, reserved]
      | some reservation =>
        have emitted := (measured_emits desc value arena physical plan size
          reservation.pointer measured converted).1
        simp only [serializeAlloc, measured, converted, reserved, emitted] at failure
        cases failure

theorem serializeAlloc_failure_unchanged (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (physical : value.Physical) (reason : Fault)
    (failure : (serializeAlloc desc value arena).written.result = .error reason)
    (before : Nat → Option UInt8) :
    applyWrites before (serializeAlloc desc value arena).written.writes = before := by
  rw [serializeAlloc_failure_writes desc value arena physical reason failure]
  rfl

theorem serializeAlloc_output (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (physical : value.Physical) (size : Nat)
    (success : (serializeAlloc desc value arena).written.result = .ok size) :
    ∃ bytes reservation, Ssz.serialize desc.erase value.erase = .ok bytes ∧ bytes.size = size ∧
      (serializeAlloc desc value arena).reservation = some (size, some reservation) ∧
      (∀ before index, (inside : index < bytes.size) →
        applyWrites before (serializeAlloc desc value arena).written.writes
          (reservation.pointer + index) = some bytes[index]) ∧
      (∀ before address, (address < reservation.pointer ∨ reservation.pointer + size ≤ address) →
        applyWrites before (serializeAlloc desc value arena).written.writes address = before address) := by
  obtain ⟨bytes, reservation, semantic, width, observed, _, _, encoded⟩ :=
    serializeAlloc_success desc value arena physical size success
  refine ⟨bytes, reservation, semantic, width, observed, ?_, ?_⟩
  · exact fun before index inside => encoded.initialized before index inside
  · intro before address outside
    apply encoded.frame before address
    simpa only [width] using outside

/-- Explicit public exclusions, in addition to the combined refinement theorem. -/
theorem serialize_no_private (desc : Desc) (value : Value) (capacity : Nat)
    (arena : Delimited.ArenaState) (physical : value.Physical) :
    (serialize desc value capacity arena).result ≠ .error .fieldIndex ∧
      ∀ available start count, (serialize desc value capacity arena).result ≠
        .error (.bounds available start count) :=
  (serialize_refines desc value capacity arena physical).no_private

theorem serializeAlloc_no_private (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (physical : value.Physical) :
    (serializeAlloc desc value arena).written.result ≠ .error .fieldIndex ∧
      ∀ available start count, (serializeAlloc desc value arena).written.result ≠
        .error (.bounds available start count) :=
  (serializeAlloc_refines desc value arena physical).no_private

theorem serialize_no_badRepresentation (desc : Desc) (value : Value) (capacity : Nat)
    (arena : Delimited.ArenaState) (physical : value.Physical) :
    (serialize desc value capacity arena).result ≠
      .error (.returned (.primitive (.arithmetic .badRepresentation))) :=
  (serialize_refines desc value capacity arena physical).no_badRepresentation

theorem serializeAlloc_no_badRepresentation (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (physical : value.Physical) :
    (serializeAlloc desc value arena).written.result ≠
      .error (.returned (.primitive (.arithmetic .badRepresentation))) :=
  (serializeAlloc_refines desc value arena physical).no_badRepresentation

end SszNative.CodecEmit

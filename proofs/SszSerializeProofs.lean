import SszSerializeMeasure

set_option autoImplicit false

namespace SszNative.Serialize

/-- A failed helper commits nothing of its own. Any earlier cursor is the input
used here, so this fact does not authorize rolling back an earlier helper. -/
theorem fromWide_failure_unchanged (arena : Delimited.ArenaState) (wide : BitVec 128)
    (reason : Error) (failed : (fromWide arena wide).result = .error reason) :
    (fromWide arena wide).used = arena.used ∧
      (NatArithmetic.fromWide arena.base arena.capacity arena.used wide).allocation = none ∧
      (NatArithmetic.fromWide arena.base arena.capacity arena.used wide).written = [] := by
  by_cases small : wide.toNat < 2 ^ 64
  · simp only [fromWide, NatArithmetic.fromWide, small, ↓reduceIte,
      NatArithmetic.unchanged, Except.mapError] at failed
    cases failed
  · cases reserved : Arena.reserve arena.base arena.capacity arena.used 2 with
    | none =>
      simp only [fromWide, NatArithmetic.fromWide, small, ↓reduceIte, reserved,
        NatArithmetic.unchanged, and_self]
    | some reservation =>
      simp only [fromWide, NatArithmetic.fromWide, small, ↓reduceIte, reserved,
        NatArithmetic.committed, Except.mapError] at failed
      cases failed

/-- Exact scratch failure, expressed using the shared native reservation rather
than an approximate capacity budget. -/
theorem fromWide_scratch_iff (arena : Delimited.ArenaState) (wide : BitVec 128) :
    (fromWide arena wide).result = .error (.arithmetic .scratchExhausted) ↔
      ¬ wide.toNat < 2 ^ 64 ∧ Arena.reserve arena.base arena.capacity arena.used 2 = none := by
  by_cases small : wide.toNat < 2 ^ 64
  · simp [fromWide, NatArithmetic.fromWide, small, NatArithmetic.unchanged, Except.mapError]
  · cases reserved : Arena.reserve arena.base arena.capacity arena.used 2 <;>
      simp [fromWide, NatArithmetic.fromWide, small, reserved,
        NatArithmetic.unchanged, NatArithmetic.committed, Except.mapError]

/-- Host conversion has no allocation or writes, including its failure path. -/
theorem encodedSize_resources (desc : Desc) (value : Value) (arena : Delimited.ArenaState) :
    (encodedSize desc value arena).used = (measure desc value arena).used ∧
      (encodedSize desc value arena).calls = (measure desc value arena).calls := by
  cases measured : (measure desc value arena).result with
  | error reason => simp only [encodedSize, bind, measured, and_self]
  | ok size =>
    unfold encodedSize bind
    rw [measured]
    dsimp only
    unfold hostSize
    split <;> simp only [unchanged, List.append_nil, and_self]

theorem encodedSize_refines_expected (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (physical : value.Physical) :
    eraseResult (encodedSize desc value arena).result = .ok (expectedSize desc value) ∨
      (encodedSize desc value arena).result = .error (.arithmetic .scratchExhausted) ∨
      (encodedSize desc value arena).result = .error .outputTooSmall := by
  rcases measure_refines desc value arena physical with measured | exhausted
  · cases result : (measure desc value arena).result with
    | error reason =>
      left
      simpa only [encodedSize, bind, result, Except.map] using measured
    | ok size =>
      have expected : expectedSize desc value = .ok size.value := by
        simpa only [result, Except.map, eraseResult, Except.ok.injEq] using measured.symm
      by_cases fits : size.value < 2 ^ 64
      · left
        simp only [encodedSize, bind, result, hostSize, fits, ↓reduceIte, unchanged,
          eraseResult, expected]
      · right; right
        simp only [encodedSize, bind, result, hostSize, fits, ↓reduceIte, unchanged]
  · right; left
    simp only [encodedSize, bind, exhausted]

/-- Public encoded_size correspondence with no successful-parse or resource
hypothesis. Each host failure remains distinguishable from pinned semantics. -/
theorem encodedSize_refines (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (physical : value.Physical) :
    eraseResult (encodedSize desc value arena).result =
        .ok ((Ssz.serialize desc.erase value.erase).map Array.size) ∨
      (encodedSize desc value arena).result = .error (.arithmetic .scratchExhausted) ∨
      (encodedSize desc value arena).result = .error .outputTooSmall := by
  rw [← expectedSize_eq_pinned]
  exact encodedSize_refines_expected desc value arena physical

theorem encodedSize_success (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (physical : value.Physical) (size : Nat)
    (success : (encodedSize desc value arena).result = .ok size) :
    expectedSize desc value = .ok size := by
  rcases encodedSize_refines_expected desc value arena physical with correct | scratch | output
  · simpa only [success, eraseResult, Except.ok.injEq] using correct.symm
  · rw [success] at scratch
    cases scratch
  · rw [success] at output
    cases output

/-- The capacity guard is after measure and host_size. A semantic or scratch
failure wins even when the output is too short. -/
theorem serialize_success_iff (desc : Desc) (value : Value) (capacity : Nat)
    (arena : Delimited.ArenaState) (size : Nat) :
    (serialize desc value capacity arena).outcome.result = .ok size ↔
      (encodedSize desc value arena).result = .ok size ∧ size ≤ capacity := by
  cases sized : (encodedSize desc value arena).result with
  | error reason => simp [serialize, sized]
  | ok actual =>
    by_cases fits : actual ≤ capacity
    · simp [serialize, sized, fits, eq_comm]
      intro same
      subst size
      exact fits
    · simp [serialize, sized, fits, eq_comm]
      intro same
      subst size
      omega

theorem serialize_success (desc : Desc) (value : Value) (capacity : Nat)
    (arena : Delimited.ArenaState) (physical : value.Physical) (size : Nat)
    (success : (serialize desc value capacity arena).outcome.result = .ok size) :
    Ssz.serialize desc.erase value.erase = .ok (serialize desc value capacity arena).writes ∧
      (serialize desc value capacity arena).writes.size = size ∧ size ≤ capacity := by
  obtain ⟨sized, fits⟩ := (serialize_success_iff desc value capacity arena size).1 success
  have expected := encodedSize_success desc value arena physical size sized
  obtain ⟨encoding, width⟩ := expected_encoding desc value
  simp only [expected, Except.map] at encoding
  simp only [serialize, sized, fits, ↓reduceIte]
  exact ⟨encoding, width size expected, True.intro⟩

/-- Serialization into caller memory never changes the measurement allocation
trace, including on output-capacity failure. -/
theorem serialize_resources (desc : Desc) (value : Value) (capacity : Nat)
    (arena : Delimited.ArenaState) :
    (serialize desc value capacity arena).outcome.used = (measure desc value arena).used ∧
      (serialize desc value capacity arena).outcome.calls = (measure desc value arena).calls := by
  have resources := encodedSize_resources desc value arena
  cases sized : (encodedSize desc value arena).result with
  | error reason => simpa only [serialize, sized] using resources
  | ok size =>
    by_cases fits : size ≤ capacity <;>
      simpa only [serialize, sized, fits, ↓reduceIte] using resources

theorem serialize_failure_writes (desc : Desc) (value : Value) (capacity : Nat)
    (arena : Delimited.ArenaState) (reason : Error)
    (failure : (serialize desc value capacity arena).outcome.result = .error reason) :
    (serialize desc value capacity arena).writes = #[] := by
  cases sized : (encodedSize desc value arena).result with
  | error fault => simp only [serialize, sized]
  | ok size =>
    by_cases fits : size ≤ capacity
    · simp only [serialize, sized, fits, ↓reduceIte] at failure
      cases failure
    · simp only [serialize, sized, fits, ↓reduceIte]

@[simp] theorem applyWrites_empty (before : Nat → Option UInt8) :
    applyWrites before #[] = before := by
  funext index
  simp [applyWrites]

theorem applyWrites_prefix (before : Nat → Option UInt8) (writes : Ssz.Bytes)
    (index : Nat) (inside : index < writes.size) :
    applyWrites before writes index = writes[index]? := by
  simp only [applyWrites, inside, ↓reduceIte]

theorem applyWrites_tail (before : Nat → Option UInt8) (writes : Ssz.Bytes)
    (index : Nat) (outside : writes.size ≤ index) :
    applyWrites before writes index = before index := by
  simp only [applyWrites, show ¬ index < writes.size by omega, ↓reduceIte]

/-- A written output byte is independent of the previous output contents. This
also covers an uninitialized byte (`none`), rather than assuming a readable buffer. -/
theorem applyWrites_no_read (left right : Nat → Option UInt8) (writes : Ssz.Bytes)
    (index : Nat) (inside : index < writes.size) :
    applyWrites left writes index = applyWrites right writes index := by
  rw [applyWrites_prefix left writes index inside, applyWrites_prefix right writes index inside]

theorem serialize_failure_unchanged (desc : Desc) (value : Value) (capacity : Nat)
    (arena : Delimited.ArenaState) (reason : Error) (before : Nat → Option UInt8)
    (failure : (serialize desc value capacity arena).outcome.result = .error reason) :
    applyWrites before (serialize desc value capacity arena).writes = before := by
  rw [serialize_failure_writes desc value capacity arena reason failure, applyWrites_empty]

/-- Exact successful byte reservation and its order: it uses the cursor after
measurement and host conversion, not the entry cursor. -/
theorem serializeAlloc_success_iff (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (size : Nat) :
    (serializeAlloc desc value arena).outcome.result = .ok size ↔
      (encodedSize desc value arena).result = .ok size ∧
        ∃ reservation, Arena.reserveBytes arena.base arena.capacity
          (encodedSize desc value arena).used size = some reservation := by
  cases sized : (encodedSize desc value arena).result with
  | error reason => simp [serializeAlloc, sized]
  | ok actual =>
    cases reserved : Arena.reserveBytes arena.base arena.capacity
        (encodedSize desc value arena).used actual with
    | none =>
      simp [serializeAlloc, sized, reserved, eq_comm]
      intro same
      subst size
      simp [reserved]
    | some reservation =>
      simp [serializeAlloc, sized, reserved, eq_comm]
      intro same
      subst size
      exact ⟨reservation, reserved.symm⟩

theorem serializeAlloc_success (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (physical : value.Physical) (size : Nat)
    (success : (serializeAlloc desc value arena).outcome.result = .ok size) :
    Ssz.serialize desc.erase value.erase = .ok (serializeAlloc desc value arena).writes ∧
      (serializeAlloc desc value arena).writes.size = size ∧
      ∃ reservation,
        Arena.reserveBytes arena.base arena.capacity (measure desc value arena).used size =
          some reservation ∧
        (serializeAlloc desc value arena).reservation = some reservation ∧
        (serializeAlloc desc value arena).outcome.used = reservation.used := by
  obtain ⟨sized, reservation, reserved⟩ :=
    (serializeAlloc_success_iff desc value arena size).1 success
  have expected := encodedSize_success desc value arena physical size sized
  obtain ⟨encoding, width⟩ := expected_encoding desc value
  have resources := encodedSize_resources desc value arena
  simp only [expected, Except.map] at encoding
  simp only [serializeAlloc, sized, reserved]
  exact ⟨encoding, width size expected, reservation, by rw [← resources.1]; exact reserved, rfl, rfl⟩

/-- This final allocation failure cannot erase count allocations or their limb
writes. No byte of the final output is written before the reservation succeeds. -/
theorem serializeAlloc_reservation_failure (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (size : Nat)
    (sized : (encodedSize desc value arena).result = .ok size)
    (failed : Arena.reserveBytes arena.base arena.capacity
      (encodedSize desc value arena).used size = none) :
    (serializeAlloc desc value arena).outcome.result = .error (.arithmetic .scratchExhausted) ∧
      (serializeAlloc desc value arena).outcome.used = (measure desc value arena).used ∧
      (serializeAlloc desc value arena).outcome.calls = (measure desc value arena).calls ∧
      (serializeAlloc desc value arena).writes = #[] := by
  have resources := encodedSize_resources desc value arena
  rw [resources.1] at failed
  simp only [serializeAlloc, sized, resources.1, failed, resources.2, and_self]

theorem serializeAlloc_failure_writes (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (reason : Error)
    (failure : (serializeAlloc desc value arena).outcome.result = .error reason) :
    (serializeAlloc desc value arena).writes = #[] := by
  cases sized : (encodedSize desc value arena).result with
  | error fault => simp only [serializeAlloc, sized]
  | ok size =>
    cases reserved : Arena.reserveBytes arena.base arena.capacity
        (encodedSize desc value arena).used size with
    | none => simp only [serializeAlloc, sized, reserved]
    | some reservation =>
      simp only [serializeAlloc, sized, reserved] at failure
      cases failure

end SszNative.Serialize

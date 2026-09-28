import SszSerializeProofs

set_option autoImplicit false

namespace SszNative.Serialize

theorem eraseResult_map {α β : Type} (result : Except Error α) (transform : α → β) :
    eraseResult (result.map transform) =
      (eraseResult result).map (fun semantic => semantic.map transform) := by
  cases result with
  | ok value => rfl
  | error reason => cases reason <;> rfl

private theorem encoding_of_size_erasure (desc : Desc) (value : Value)
    (result : Except Error Nat)
    (correct : eraseResult result = .ok (expectedSize desc value)) :
    eraseResult (result.map (fun _ => emit desc value)) =
      .ok (Ssz.serialize desc.erase value.erase) := by
  rw [eraseResult_map, correct]
  simp only [Except.map, (expected_encoding desc value).1]

/-- Public serialize correspondence for all semantic and resource outcomes. The
resource alternatives are not treated as SSZ errors; their exact ordered guards
and retained allocations are specified separately below and in serialize_resources. -/
theorem serialize_refines (desc : Desc) (value : Value) (capacity : Nat)
    (arena : Delimited.ArenaState) (physical : value.Physical) :
    eraseResult ((serialize desc value capacity arena).outcome.result.map
        (fun _ => (serialize desc value capacity arena).writes)) =
        .ok (Ssz.serialize desc.erase value.erase) ∨
      (serialize desc value capacity arena).outcome.result =
        .error (.arithmetic .scratchExhausted) ∨
      (serialize desc value capacity arena).outcome.result = .error .outputTooSmall := by
  rcases encodedSize_refines_expected desc value arena physical with correct | scratch | output
  · have encoding := encoding_of_size_erasure desc value
      (encodedSize desc value arena).result correct
    cases sized : (encodedSize desc value arena).result with
    | error reason =>
      left
      simpa only [serialize, sized, Except.map] using encoding
    | ok size =>
      by_cases fits : size ≤ capacity
      · left
        simpa only [serialize, sized, fits, ↓reduceIte, Except.map] using encoding
      · right; right
        simp only [serialize, sized, fits, ↓reduceIte]
  · right; left
    simp only [serialize, scratch]
  · right; right
    simp only [serialize, output]

/-- Public serialize_alloc correspondence, including count-allocation failures,
semantic rejection, host conversion, and final byte allocation. -/
theorem serializeAlloc_refines (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (physical : value.Physical) :
    eraseResult ((serializeAlloc desc value arena).outcome.result.map
        (fun _ => (serializeAlloc desc value arena).writes)) =
        .ok (Ssz.serialize desc.erase value.erase) ∨
      (serializeAlloc desc value arena).outcome.result =
        .error (.arithmetic .scratchExhausted) ∨
      (serializeAlloc desc value arena).outcome.result = .error .outputTooSmall := by
  rcases encodedSize_refines_expected desc value arena physical with correct | scratch | output
  · have encoding := encoding_of_size_erasure desc value
      (encodedSize desc value arena).result correct
    cases sized : (encodedSize desc value arena).result with
    | error reason =>
      left
      simpa only [serializeAlloc, sized, Except.map] using encoding
    | ok size =>
      cases reserved : Arena.reserveBytes arena.base arena.capacity
          (encodedSize desc value arena).used size with
      | none => right; left; simp only [serializeAlloc, sized, reserved]
      | some reservation =>
        left
        simpa only [serializeAlloc, sized, reserved, Except.map] using encoding
  · right; left
    simp only [serializeAlloc, scratch]
  · right; right
    simp only [serializeAlloc, output]

/-- The count's actual two-limb reservation, with every overflow/alignment guard
in Arena.reserve. This predicate does not truncate the logical count. -/
def WideExhausted (arena : Delimited.ArenaState) (wide : BitVec 128) : Prop :=
  ¬ wide.toNat < 2 ^ 64 ∧ Arena.reserve arena.base arena.capacity arena.used 2 = none

/-- Once the first count exists, only a passing bound permits the second helper.
A first-helper scratch failure wins over any semantic over-limit rejection. -/
def ListExhausted (limit : Option NatOperand) (bits : Packed)
    (arena : Delimited.ArenaState) : Prop :=
  match (fromWide arena bits.count).result with
  | .error _ => WideExhausted arena bits.count
  | .ok actual =>
    (match limit with | none => True | some cap => actual.value ≤ cap.value) ∧
      WideExhausted { arena with used := (fromWide arena bits.count).used }
        (BitVec.ofNat 128 (bits.count.toNat / 8 + 1))

/-- All non-bit-list leaves are allocation-free, except that a bit-vector scope
error materializes its actual count before returning the error. -/
def MeasureExhausted (desc : Desc) (value : Value) (arena : Delimited.ArenaState) : Prop :=
  match desc, value with
  | .bitVector length, .bits bits =>
    length.value ≠ bits.count.toNat ∧ WideExhausted arena bits.count
  | .bitList limit, .bits bits => ListExhausted (some limit) bits arena
  | .progressiveBitList limit, .bits bits => ListExhausted limit bits arena
  | _, _ => False

theorem measureList_scratch_iff (limit : Option NatOperand) (bits : Packed)
    (arena : Delimited.ArenaState) :
    (measureList limit bits arena).result = .error (.arithmetic .scratchExhausted) ↔
      ListExhausted limit bits arena := by
  rcases fromWide_cases arena bits.count with ⟨actual, success, value⟩ | exhausted
  · cases limit with
    | none =>
      simp only [measureList, bind, success, bounded, unchanged, ListExhausted,
        true_and, fromWide_scratch_iff, WideExhausted]
    | some cap =>
      by_cases fits : actual.value ≤ cap.value
      · simp only [measureList, bind, success, bounded, fits, ↓reduceIte, unchanged,
          ListExhausted, true_and, fromWide_scratch_iff, WideExhausted]
      · simp [measureList, bind, success, bounded, fits, unchanged, ListExhausted]
  · have failed := (fromWide_scratch_iff arena bits.count).1 exhausted
    simp [measureList, bind, exhausted, ListExhausted, WideExhausted, failed]

/-- Exact iff, not merely 'sufficient scratch implies correctness'. It includes
the ordering that can allocate even on a semantic rejection. -/
theorem measure_scratch_iff (desc : Desc) (value : Value) (arena : Delimited.ArenaState) :
    (measure desc value arena).result = .error (.arithmetic .scratchExhausted) ↔
      MeasureExhausted desc value arena := by
  cases desc <;> cases value <;>
    simp only [measure, MeasureExhausted]
  all_goals try { exact iff_false_intro (by intro impossible; cases impossible) }
  · split <;> simp [unchanged]
  · split <;> simp [unchanged]
  · rename_i cap bytes
    by_cases fits : (count bytes.size).value ≤ cap.value <;>
      simp [bounded, fits, unchanged, bind]
  · rename_i length bits
    by_cases same : length.value = bits.count.toNat
    · simp [same, unchanged]
    · simp only [same, ↓reduceIte]
      rcases fromWide_cases arena bits.count with ⟨actual, success, value⟩ | exhausted
      · have notFailed : ¬ WideExhausted arena bits.count := by
          intro failed
          have failure := (fromWide_scratch_iff arena bits.count).2 failed
          rw [success] at failure
          cases failure
        simp [bind, success, unchanged, notFailed]
      · have failed := (fromWide_scratch_iff arena bits.count).1 exhausted
        simp [bind, exhausted, WideExhausted, failed]
        exact same
  · exact measureList_scratch_iff _ _ _
  · exact measureList_scratch_iff _ _ _

/-- Host narrowing can only add OutputTooSmall, never scratch failure. -/
theorem encodedSize_scratch_iff (desc : Desc) (value : Value) (arena : Delimited.ArenaState) :
    (encodedSize desc value arena).result = .error (.arithmetic .scratchExhausted) ↔
      MeasureExhausted desc value arena := by
  rw [← measure_scratch_iff]
  cases measured : (measure desc value arena).result with
  | error reason => simp [encodedSize, bind, measured]
  | ok size =>
    by_cases fits : size.value < 2 ^ 64 <;>
      simp [encodedSize, bind, measured, hostSize, fits, unchanged]

/-- The caller output capacity is consulted only when encoded_size succeeded. -/
theorem serialize_scratch_iff (desc : Desc) (value : Value) (capacity : Nat)
    (arena : Delimited.ArenaState) :
    (serialize desc value capacity arena).outcome.result = .error (.arithmetic .scratchExhausted) ↔
      MeasureExhausted desc value arena := by
  rw [← encodedSize_scratch_iff]
  cases sized : (encodedSize desc value arena).result with
  | error reason => simp only [serialize, sized]
  | ok size =>
    by_cases fits : size ≤ capacity <;> simp [serialize, sized, fits]

/-- Final-byte allocation is the only additional scratch-failure source. Its
positive-isize bound is physical, and does not restrict any logical SSZ cap. -/
theorem serializeAlloc_scratch_iff (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) :
    (serializeAlloc desc value arena).outcome.result = .error (.arithmetic .scratchExhausted) ↔
      MeasureExhausted desc value arena ∨
      ∃ size, (encodedSize desc value arena).result = .ok size ∧
        Arena.reserveBytes arena.base arena.capacity (encodedSize desc value arena).used size = none := by
  rw [← encodedSize_scratch_iff]
  cases sized : (encodedSize desc value arena).result with
  | error reason => simp [serializeAlloc, sized]
  | ok size =>
    cases reserved : Arena.reserveBytes arena.base arena.capacity
        (encodedSize desc value arena).used size <;> simp [serializeAlloc, sized, reserved]

theorem bounded_resources (limit : Option NatOperand) (actual : NatOperand) (used : Nat) :
    (bounded limit actual used).used = used ∧ (bounded limit actual used).calls = [] := by
  cases limit with
  | none => exact ⟨rfl, rfl⟩
  | some cap =>
    by_cases fits : actual.value ≤ cap.value <;>
      simp only [bounded, fits, ↓reduceIte, unchanged, and_self]

/-- Over-limit error retains the materialized count's representation, reservation,
written limbs, and new cursor; it performs no width construction afterward. -/
theorem measureList_limit_no_rollback (cap actual : NatOperand) (bits : Packed)
    (arena : Delimited.ArenaState)
    (counted : (fromWide arena bits.count).result = .ok actual)
    (over : ¬ actual.value ≤ cap.value) :
    measureList (some cap) bits arena =
      ⟨.error (.limit cap actual), (fromWide arena bits.count).used,
        [NatArithmetic.fromWide arena.base arena.capacity arena.used bits.count]⟩ := by
  simp only [measureList, bind, counted, bounded, over, ↓reduceIte, unchanged,
    List.append_nil] <;> rfl

/-- Exact two-helper trace after a passing bound, whether the second helper
succeeds or fails. Nonallocating Small results still record the actual call. -/
theorem measureList_after_bound (limit : Option NatOperand) (actual : NatOperand)
    (bits : Packed) (arena : Delimited.ArenaState)
    (counted : (fromWide arena bits.count).result = .ok actual)
    (checked : (bounded limit actual (fromWide arena bits.count).used).result = .ok ()) :
    measureList limit bits arena =
      let next := fromWide { arena with used := (fromWide arena bits.count).used }
        (BitVec.ofNat 128 (bits.count.toNat / 8 + 1))
      ⟨next.result, next.used,
        [NatArithmetic.fromWide arena.base arena.capacity arena.used bits.count] ++ next.calls⟩ := by
  have resources := bounded_resources limit actual (fromWide arena bits.count).used
  simp only [measureList, bind, counted, checked, resources.1, resources.2,
    List.nil_append] <;> rfl

/-- A second reservation failure leaves the first committed cursor and its exact
limb writes. The failed call is retained as the second trace entry. -/
theorem measureList_second_failure_no_rollback (limit : Option NatOperand)
    (actual : NatOperand) (bits : Packed) (arena : Delimited.ArenaState)
    (counted : (fromWide arena bits.count).result = .ok actual)
    (checked : (bounded limit actual (fromWide arena bits.count).used).result = .ok ())
    (failed : (fromWide { arena with used := (fromWide arena bits.count).used }
      (BitVec.ofNat 128 (bits.count.toNat / 8 + 1))).result =
        .error (.arithmetic .scratchExhausted)) :
    (measureList limit bits arena).used = (fromWide arena bits.count).used ∧
      (measureList limit bits arena).calls =
        [NatArithmetic.fromWide arena.base arena.capacity arena.used bits.count,
         NatArithmetic.fromWide arena.base arena.capacity (fromWide arena bits.count).used
           (BitVec.ofNat 128 (bits.count.toNat / 8 + 1))] := by
  rw [measureList_after_bound limit actual bits arena counted checked]
  have unchanged := fromWide_failure_unchanged
    { arena with used := (fromWide arena bits.count).used }
    (BitVec.ofNat 128 (bits.count.toNat / 8 + 1)) (.arithmetic .scratchExhausted) failed
  exact ⟨unchanged.1, rfl⟩

/-- Zero final output uses byte dangling pointer one without padding or cursor
movement, even if the arena's positive-allocation arithmetic would fail. -/
theorem serializeAlloc_zero (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (sized : (encodedSize desc value arena).result = .ok 0) :
    (serializeAlloc desc value arena).reservation =
        some ⟨1, (measure desc value arena).used⟩ ∧
      (serializeAlloc desc value arena).outcome.used = (measure desc value arena).used := by
  have resources := encodedSize_resources desc value arena
  simp only [serializeAlloc, sized, Arena.reserveBytes_zero, resources.1, and_self]

theorem measure_not_outputTooSmall (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (physical : value.Physical) :
    (measure desc value arena).result ≠ .error .outputTooSmall := by
  intro failed
  rcases measure_refines desc value arena physical with correct | scratch
  · simp only [failed, Except.map, eraseResult] at correct
    cases correct
  · rw [failed] at scratch
    cases scratch

/-- Logical encoded widths are not capped: only their conversion to the native
usize return type can cause encoded_size's OutputTooSmall. -/
theorem encodedSize_output_iff (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (physical : value.Physical) :
    (encodedSize desc value arena).result = .error .outputTooSmall ↔
      ∃ size, (measure desc value arena).result = .ok size ∧ ¬ size.value < 2 ^ 64 := by
  cases measured : (measure desc value arena).result with
  | error reason =>
    have notOutput := measure_not_outputTooSmall desc value arena physical
    rw [measured] at notOutput
    simp [encodedSize, bind, measured]
    intro same
    cases same
    exact notOutput rfl
  | ok size =>
    by_cases fits : size.value < 2 ^ 64 <;>
      simp [encodedSize, bind, measured, hostSize, fits, unchanged] <;> omega

theorem serialize_output_iff (desc : Desc) (value : Value) (capacity : Nat)
    (arena : Delimited.ArenaState) :
    (serialize desc value capacity arena).outcome.result = .error .outputTooSmall ↔
      (encodedSize desc value arena).result = .error .outputTooSmall ∨
      ∃ size, (encodedSize desc value arena).result = .ok size ∧ ¬ size ≤ capacity := by
  cases sized : (encodedSize desc value arena).result with
  | error reason => simp [serialize, sized]
  | ok size =>
    by_cases fits : size ≤ capacity <;> simp [serialize, sized, fits] <;> omega

theorem serializeAlloc_output_iff (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) :
    (serializeAlloc desc value arena).outcome.result = .error .outputTooSmall ↔
      (encodedSize desc value arena).result = .error .outputTooSmall := by
  cases sized : (encodedSize desc value arena).result with
  | error reason => simp only [serializeAlloc, sized]
  | ok size =>
    cases reserved : Arena.reserveBytes arena.base arena.capacity
        (encodedSize desc value arena).used size <;> simp [serializeAlloc, sized, reserved]

end SszNative.Serialize

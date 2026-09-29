import SszCodecDecodeStructSlots

set_option autoImplicit false

namespace SszNative.CodecDecode

open Codec (Desc Error)

private theorem struct_throw_error {α : Type} (fault : Ssz.Err) :
    (throw fault : Except Ssz.Err α) = .error fault := rfl

/-- The pinned header checks, with the span values erased only after their
complete ordered validation. -/
def structValidation (offsets : List Nat) (leading scope : Nat) : Except Ssz.Err Unit :=
  match offsets with
  | [] => if scope = leading then .ok () else .error (.scope leading scope)
  | first :: rest =>
    if first ≠ leading then .error (.firstOffset leading first)
    else (Ssz.offsetSpans (first :: rest) scope).map fun _ => ()

/-- A pending variable field scans every descending pair before checking the
last offset against scope, exactly as `offsetSpans`. -/
theorem validateSlots_pending {children : List Desc} (entries : List (Entry children))
    (data : Ssz.Bytes) (allocation : Arena.Reservation) (index leading scope : Nat)
    (previousIndex : Nat) (previous : Slot) (used : Nat) :
    Codec.eraseResult (validateSlots entries allocation index leading scope
      (some (previousIndex, previous)) used).result =
      .ok ((Ssz.offsetSpans (previous.start :: Ssz.bodyStarts (entrySlots data entries)) scope).map
        fun _ => ()) := by
  induction entries generalizing index previousIndex previous used with
  | nil =>
    by_cases past : scope < previous.start <;>
      simp only [validateSlots, entrySlots, List.map_nil, Ssz.bodyStarts,
        Ssz.offsetSpans, past, ↓reduceIte, unchanged, writeSlot, Codec.eraseResult, Except.map]
  | cons entry rest ih =>
    cases width : entry.slot.width with
    | some number =>
      simpa only [validateSlots, width, entrySlots, List.map_cons, entrySlot,
        width, Ssz.bodyStarts] using ih (index + 1) previousIndex previous used
    | none =>
      by_cases descending : entry.slot.start < previous.start
      · simp only [validateSlots, ↓reduceIte, unchanged,
          Codec.eraseResult, entrySlots, List.map_cons, entrySlot, width,
          Ssz.bodyStarts, Ssz.offsetSpans, descending, Except.map]
      · simp only [validateSlots, ↓reduceIte, bind, writeSlot,
          entrySlots, List.map_cons, entrySlot, width, Ssz.bodyStarts, Ssz.offsetSpans,
          descending, Bind.bind, Except.bind]
        rw [ih (index + 1) index entry.slot used]
        simp only [entrySlots]
        cases Ssz.offsetSpans (entry.slot.start :: Ssz.bodyStarts (rest.map (entrySlot data))) scope <;> rfl

theorem validateSlots_refines {children : List Desc} (entries : List (Entry children))
    (data : Ssz.Bytes) (allocation : Arena.Reservation) (index leading used : Nat)
    (physical : data.size < 2 ^ 64) (front : leading < 2 ^ 64)
    (safe : positionedSafe entries data.size) :
    Codec.eraseResult (validateSlots entries allocation index leading data.size none used).result =
      .ok (structValidation (Ssz.bodyStarts (entrySlots data entries)) leading data.size) := by
  induction entries generalizing index used with
  | nil =>
    by_cases same : leading = data.size
    · simp [validateSlots, exact, count_value data.size physical, same,
        unchanged, Codec.eraseResult, structValidation, entrySlots, Ssz.bodyStarts]
    · have reverse : data.size ≠ leading := Ne.symm same
      simp [validateSlots, exact, count_value leading front, same, reverse,
        unchanged, Codec.eraseResult, Serialize.eraseResult,
        count_value data.size physical, structValidation, entrySlots, Ssz.bodyStarts]
  | cons entry rest ih =>
    have tailSafe : positionedSafe rest data.size := fun next member => safe next (by simp [member])
    cases width : entry.slot.width with
    | some number =>
      simpa only [validateSlots, width, entrySlots, List.map_cons, entrySlot,
        width, Ssz.bodyStarts] using ih (index + 1) used tailSafe
    | none =>
      have startPhysical : entry.slot.start < 2 ^ 64 := by
        simpa only [width] using safe entry (by simp)
      by_cases first : entry.slot.start = leading
      · simp only [validateSlots, width, entrySlots, List.map_cons, entrySlot,
          Ssz.bodyStarts, structValidation, first, ne_eq, not_true_eq_false, ↓reduceIte]
        simpa only [first, entrySlots] using
          validateSlots_pending rest data allocation (index + 1) leading data.size index entry.slot used
      · simp [validateSlots, width, first, unchanged, Codec.eraseResult,
          count_value leading front, count_value entry.slot.start startPhysical,
          entrySlots, entrySlot, Ssz.bodyStarts, structValidation]

def structFinish (slots : List Ssz.Slot) (leading : Nat) (data : Ssz.Bytes) : Except Ssz.Err (List Ssz.Bytes) := do
  let offsets := Ssz.bodyStarts slots
  if offsets.isEmpty then
    if data.size != leading then throw (.scope leading data.size)
    return slots.map Ssz.Slot.held
  if offsets[0]! != leading then throw (.firstOffset leading offsets[0]!)
  let spans ← Ssz.offsetSpans offsets data.size
  Ssz.takeSlots data slots spans

theorem closeSlots_noBodies {children : List Desc} (entries : List (Entry children))
    (data : Ssz.Bytes) (empty : Ssz.bodyStarts (entrySlots data entries) = []) :
    entrySlices data (closeSlots entries data.size) = (entrySlots data entries).map Ssz.Slot.held := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    cases width : entry.slot.width with
    | none => simp [entrySlots, entrySlot, width, Ssz.bodyStarts] at empty
    | some number =>
      have tailEmpty : Ssz.bodyStarts (entrySlots data rest) = [] := by
        simpa only [entrySlots, List.map_cons, entrySlot, width, Ssz.bodyStarts] using empty
      simpa only [closeSlots, width, Option.isSome, ↓reduceIte, entrySlices,
        List.map_cons, entrySlots, entrySlot, width, Ssz.Slot.held] using
        congrArg (data.extract entry.slot.start entry.slot.ending :: ·) (ih tailEmpty)

/-- Successful validation is sufficient for the full pinned slice computation;
no premise predicts a future child decode. -/
theorem structFinish_validation {children : List Desc} (entries : List (Entry children))
    (data : Ssz.Bytes) (leading : Nat) :
    structFinish (entrySlots data entries) leading data =
      (structValidation (Ssz.bodyStarts (entrySlots data entries)) leading data.size).bind
        (fun _ => .ok (entrySlices data (closeSlots entries data.size))) := by
  cases offsets : Ssz.bodyStarts (entrySlots data entries) with
  | nil =>
    have parts := closeSlots_noBodies entries data offsets
    rw [parts]
    by_cases same : data.size = leading <;>
      simp [structFinish, structValidation, offsets, same, struct_throw_error,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
  | cons first rest =>
    by_cases same : first = leading
    · simp only [structFinish, offsets, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        List.getElem!_cons_zero, same, bne_self_eq_false, structValidation, ne_eq,
        not_true_eq_false, Bind.bind, Except.bind]
      change (Ssz.offsetSpans (leading :: rest) data.size).bind
          (fun spans => Ssz.takeSlots data (entrySlots data entries) spans) =
        ((Ssz.offsetSpans (leading :: rest) data.size).map (fun _ => ())).bind
          (fun _ => .ok (entrySlices data (closeSlots entries data.size)))
      cases spans : Ssz.offsetSpans (leading :: rest) data.size with
      | error reason => rfl
      | ok widths =>
        have read : Ssz.offsetSpans (Ssz.bodyStarts (entrySlots data entries)) data.size = .ok widths := by
          simpa only [offsets, same] using spans
        simpa only [spans, Bind.bind, Except.bind, Except.map] using closeSlots_takeSlots entries data widths read
    · simp [structFinish, structValidation, offsets, same, struct_throw_error,
        Bind.bind, Except.bind] <;> rfl

/-- Validation erases to the entire pinned finishing phase while its successful
result still refers to the actual closed native entries. -/
theorem validateSlots_finish_refines {children : List Desc} (entries : List (Entry children))
    (data : Ssz.Bytes) (allocation : Arena.Reservation) (index leading used : Nat)
    (physical : data.size < 2 ^ 64) (front : leading < 2 ^ 64)
    (safe : positionedSafe entries data.size) :
    Refines (fun _ : Unit => entrySlices data (closeSlots entries data.size))
      (validateSlots entries allocation index leading data.size none used)
      (structFinish (entrySlots data entries) leading data) := by
  have correct := validateSlots_refines entries data allocation index leading used physical front safe
  rw [structFinish_validation]
  left
  rw [Codec.eraseResult_map, correct]
  cases structValidation (Ssz.bodyStarts (entrySlots data entries)) leading data.size <;> rfl

theorem structSlices_eq (fields : List Ssz.Desc) (data : Ssz.Bytes)
    (composite : data.size < 2 ^ 32) :
    Ssz.structSlices fields data = (Ssz.structBudget fields data.size).bind fun _ =>
      (Ssz.readSlots fields data 0).bind fun result => structFinish result.1 result.2 data := by
  simp only [Ssz.structSlices, Ssz.bytesPerOffset, show 8 * 4 = 32 by decide,
    show ¬ data.size ≥ 2 ^ 32 by omega, ↓reduceIte, Bind.bind, Except.bind,
    Pure.pure, Except.pure, structFinish] <;>
    cases Ssz.structBudget fields data.size <;> simp only [Except.bind] <;>
    cases Ssz.readSlots fields data 0 <;> rfl

theorem closeSlots_safe_of_validate {children : List Desc} (entries : List (Entry children))
    (data : Ssz.Bytes) (allocation : Arena.Reservation) (index leading used : Nat)
    (physical : data.size < 2 ^ 64) (front : leading < 2 ^ 64)
    (safe : positionedSafe entries data.size)
    (success : (validateSlots entries allocation index leading data.size none used).result = .ok ()) :
    ∀ entry ∈ closeSlots entries data.size,
      entry.slot.start ≤ entry.slot.ending ∧ entry.slot.ending ≤ data.size := by
  have correct := validateSlots_refines entries data allocation index leading used physical front safe
  simp only [success, Codec.eraseResult, Except.ok.injEq] at correct
  have spans : ∃ spans, Ssz.offsetSpans (Ssz.bodyStarts (entrySlots data entries)) data.size = .ok spans := by
    cases offsets : Ssz.bodyStarts (entrySlots data entries) with
    | nil => exact ⟨[], rfl⟩
    | cons first rest =>
      simp only [structValidation, offsets] at correct
      split at correct
      · cases correct
      · cases read : Ssz.offsetSpans (first :: rest) data.size with
        | error reason =>
          simp only [read, Except.map] at correct
          cases correct
        | ok widths => exact ⟨widths, rfl⟩
  obtain ⟨spans, read⟩ := spans
  exact closeSlots_safe entries data spans safe read

end SszNative.CodecDecode

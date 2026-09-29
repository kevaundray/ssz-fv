import SszCodecDecodeRefinementCore
import Ssz.Proofs.Codec.Table

set_option autoImplicit false

namespace SszNative.CodecDecode

open Codec (Desc Error)

theorem sequence_bind_ok {α β γ δ : Type} (eraseFirst : α → γ) (eraseNext : β → δ)
    (first : Outcome α) (next : α → Nat → Outcome β) (value : γ)
    (expected : Except Ssz.Err δ)
    (firstRefines : Refines eraseFirst first (.ok value))
    (nextRefines : ∀ actual used, eraseFirst actual = value →
      Refines eraseNext (next actual used) expected) :
    Refines eraseNext (bind first next) expected := by
  rcases firstRefines with correct | exhausted
  · cases result : first.result with
    | ok actual =>
      have equal : eraseFirst actual = value := by
        simpa only [result, Except.map, Codec.eraseResult, Except.ok.injEq] using correct
      simpa only [Refines, bind, result] using nextRefines actual first.used equal
    | error reason =>
      cases reason with
      | primitive reason => cases reason <;>
          simp [result, Except.map, Codec.eraseResult, Serialize.eraseResult] at correct
      | offsetOverflow _ | unknownSelector _ | scopeTooSmall _ _ | scopeUndivided _ _
      | scopeWidthless | firstOffset _ _ | offsetUnordered | offsetPastScope
      | offsetUnaligned | offsetBelowTable | truncated | notABit _ | paddingBits
      | emptyEncoding | noDelimiter | trailingZeros | noSelector =>
          simp [result, Except.map, Codec.eraseResult] at correct
  · exact Or.inr (by simp only [bind, exhausted])

theorem sequence_mul_refines (left right : NatOperand) (arena : Delimited.ArenaState) :
    Refines NatOperand.value (mul left right arena) (.ok (left.value * right.value)) := by
  cases result : (NatMul.run left right arena.base arena.capacity arena.used).result with
  | ok value =>
    have correct := NatMul.run_value left right arena.base arena.capacity arena.used value result
    exact Or.inl (by simp only [mul, result, Except.mapError, Except.map,
      Codec.eraseResult, correct])
  | error reason =>
    cases reason with
    | scratchExhausted => exact Or.inr (by simp only [mul, result, Except.mapError, scratch])
    | badRepresentation =>
      exact False.elim (NatMul.no_badRepresentation left right arena.base arena.capacity arena.used result)

theorem sequence_bounded_refines (limit : Option NatOperand) (actual : NatOperand) (used : Nat) :
    Refines (fun value : Unit => value) (bounded limit actual used)
      (match limit with
       | none => .ok ()
       | some cap => if cap.value < actual.value then .error (.overLimit cap.value actual.value)
           else .ok ()) := by
  cases limit with
  | none => exact Or.inl rfl
  | some cap =>
    by_cases within : actual.value ≤ cap.value
    · left
      simp only [bounded, Serialize.bounded, within, ↓reduceIte, Serialize.unchanged,
        Except.mapError, Except.map, Codec.eraseResult, Nat.not_lt.mpr within]
    · have over : cap.value < actual.value := by omega
      left
      simp only [bounded, Serialize.bounded, within, ↓reduceIte, Serialize.unchanged,
        Except.mapError, Except.map, Codec.eraseResult, Serialize.eraseResult, over]

theorem sequence_slice_physical (input : Input) (start ending : Nat)
    (physical : input.bytes.size < 2 ^ 64) :
    (input.slice start ending).bytes.size < 2 ^ 64 := by
  simp only [Input.slice, Array.size_extract]
  omega

/-- The table reader never needs the totalized out-of-range byte case. -/
theorem sequence_table_read_bounds (count scope index byte : Nat)
    (table : count * 4 ≤ scope) (entry : index < count) (within : byte < 4) :
    index * 4 + byte < scope := by
  have bound := Nat.mul_le_mul_right 4 (show index + 1 ≤ count by omega)
  omega

theorem sequence_table_machine_reads (input : Input) (count index byte : Nat)
    (physical : input.bytes.size < 2 ^ 64) (table : count * 4 ≤ input.bytes.size)
    (entry : index < count) (within : byte < 4) :
    index * 4 + byte < input.bytes.size ∧ index * 4 + byte < 2 ^ 64 := by
  have bound := sequence_table_read_bounds count input.bytes.size index byte table entry within
  exact ⟨bound, Nat.lt_trans bound physical⟩

theorem sequence_first_offset_read (count scope : Nat)
    (positive : 0 < count) (table : count * 4 ≤ scope) :
    ∀ byte < 4, byte < scope := by
  intro byte within
  simpa only [Nat.zero_mul, Nat.zero_add] using
    sequence_table_read_bounds count scope 0 byte table positive within

theorem sequence_fixed_window_bounds (count width scope : Nat)
    (fits : count * width ≤ scope) (window : Window)
    (member : window ∈ fixedWindows count width) :
    window.start ≤ window.ending ∧ window.ending ≤ scope := by
  simp only [fixedWindows, List.mem_map] at member
  rcases member with ⟨index, member, rfl⟩
  have indexBound : index + 1 ≤ count := by
    have below : index < count := List.mem_range.mp member
    omega
  have bound := Nat.mul_le_mul_right width indexBound
  simp only [Nat.add_mul, Nat.one_mul] at bound
  exact ⟨Nat.le_add_right _ _, Nat.le_trans bound fits⟩

/-- A declared vector's complete offset table lies before the first body. -/
theorem sequence_vector_table_bounds (count scope : Nat)
    (leading : ¬ scope < count * 4) :
    count * 4 ≤ scope ∧
      (∀ index < count, ∀ byte < 4, index * 4 + byte < scope) := by
  have table : count * 4 ≤ scope := by omega
  exact ⟨table, fun index entry byte within =>
    sequence_table_read_bounds count scope index byte table entry within⟩

/-- Alignment is needed for equality with the table boundary, not for rounding
the physical read budget up. No byte outside the actual table is read. -/
theorem sequence_list_table_bounds (first scope : Nat)
    (aligned : first % 4 = 0) (within : ¬ scope < first) :
    (first / 4) * 4 = first ∧
      (∀ index < first / 4, ∀ byte < 4, index * 4 + byte < scope) := by
  have width : (first / 4) * 4 = first := by omega
  exact ⟨width, fun index entry byte byteBound =>
    sequence_table_read_bounds (first / 4) scope index byte (by omega) entry byteBound⟩

theorem sequence_list_fixed_windows (scope width : Nat)
    (divided : scope % width = 0) (window : Window)
    (member : window ∈ fixedWindows (scope / width) width) :
    window.start ≤ window.ending ∧ window.ending ≤ scope := by
  apply sequence_fixed_window_bounds (scope / width) width scope _ window member
  exact Nat.le_of_eq (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero divided))

/-- Genuine bounded windows preserve both the borrowed offset and byte length;
the extractor's clipping cases are unreachable under this premise. -/
theorem sequence_slice_window (input : Input) (window : Window)
    (ordered : window.start ≤ window.ending) (bounded : window.ending ≤ input.bytes.size) :
    (input.slice window.start window.ending).offset = input.offset + window.start ∧
    (input.slice window.start window.ending).bytes.size = window.ending - window.start ∧
    (input.slice window.start window.ending).offset +
      (input.slice window.start window.ending).bytes.size ≤ input.offset + input.bytes.size := by
  refine ⟨rfl, Array.size_extract_of_le bounded, ?_⟩
  change input.offset + window.start +
    (input.bytes.extract window.start window.ending).size ≤ input.offset + input.bytes.size
  rw [Array.size_extract_of_le bounded]
  omega

theorem sequence_window_machine_bounds (input : Input) (window : Window)
    (physical : input.bytes.size < 2 ^ 64)
    (ordered : window.start ≤ window.ending) (bounded : window.ending ≤ input.bytes.size) :
    window.start < 2 ^ 64 ∧ window.ending < 2 ^ 64 := by
  omega

theorem validateOffsets_refines (offsets : List Nat) (scope : Nat) :
    Codec.eraseResult (validateOffsets offsets scope) =
      .ok ((Ssz.offsetSpans offsets scope).map (fun _ => ())) := by
  induction offsets with
  | nil => rfl
  | cons start rest ih =>
    cases rest with
    | nil =>
      by_cases past : scope < start <;>
        simp [validateOffsets, Ssz.offsetSpans, past, Codec.eraseResult, Except.map]
    | cons next rest =>
      by_cases descending : next < start
      · simp [validateOffsets, Ssz.offsetSpans, descending, Codec.eraseResult, Except.map]
      · simp only [validateOffsets, Ssz.offsetSpans, descending, ↓reduceIte]
        rw [ih]
        cases Ssz.offsetSpans (next :: rest) scope <;> rfl

/-- Validation establishes genuine windows, not merely safe clipped extraction. -/
theorem sequence_offset_window_bounds (offsets : List Nat) (scope : Nat)
    (valid : validateOffsets offsets scope = .ok ()) :
    ∀ window ∈ offsetWindows offsets scope,
      window.start ≤ window.ending ∧ window.ending ≤ scope := by
  revert valid
  induction offsets with
  | nil => intro valid; simp [offsetWindows]
  | cons start rest ih =>
    intro valid
    cases rest with
    | nil =>
      simp only [validateOffsets] at valid
      have bound : start ≤ scope := by split at valid <;> simp_all <;> omega
      simpa only [offsetWindows, List.mem_singleton] using
        (fun window (equal : window = (⟨start, scope⟩ : Window)) => by
          subst window; exact And.intro bound (Nat.le_refl scope))
    | cons next rest =>
      have ordered : start ≤ next := by
        by_cases descending : next < start
        · simp [validateOffsets, descending] at valid
        · omega
      have tailValid : validateOffsets (next :: rest) scope = .ok () := by
        simpa only [validateOffsets, show ¬ next < start by omega, ↓reduceIte] using valid
      have tailBounds := ih tailValid
      have nextBound : next ≤ scope := by
        cases rest with
        | nil => exact (tailBounds ⟨next, scope⟩ (by simp [offsetWindows])).1
        | cons ending rest =>
          have bounds := tailBounds ⟨next, ending⟩ (by simp [offsetWindows])
          exact Nat.le_trans bounds.1 bounds.2
      intro window member
      simp only [offsetWindows, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨ordered, nextBound⟩
      · exact tailBounds window member

theorem sequence_offset_extracts (offsets spans : List Nat) (scope : Nat) (data : Ssz.Bytes)
    (valid : Ssz.offsetSpans offsets scope = .ok spans) :
    (offsetWindows offsets scope).map (fun window => data.extract window.start window.ending) =
      (offsets.zip spans).map (fun pair => data.extract pair.1 (pair.1 + pair.2)) := by
  induction offsets generalizing spans with
  | nil => cases valid; rfl
  | cons start rest ih =>
    cases rest with
    | nil =>
      by_cases past : scope < start
      · simp [Ssz.offsetSpans, past] at valid
      · simp only [Ssz.offsetSpans, past, ↓reduceIte, Except.ok.injEq] at valid
        subst spans
        simp [offsetWindows, Nat.add_sub_of_le (show start ≤ scope by omega)]
    | cons next rest =>
      by_cases descending : next < start
      · simp [Ssz.offsetSpans, descending] at valid
      · cases tail : Ssz.offsetSpans (next :: rest) scope with
        | error reason =>
          simp only [Ssz.offsetSpans, descending, ↓reduceIte, tail] at valid
          change Except.error reason = Except.ok spans at valid
          cases valid
        | ok widths =>
          simp only [Ssz.offsetSpans, descending, ↓reduceIte, tail] at valid
          change Except.ok ((next - start) :: widths) = Except.ok spans at valid
          have equal := Except.ok.inj valid
          subst spans
          simp only [offsetWindows, List.map_cons, List.zip_cons_cons]
          rw [Nat.add_sub_of_le (show start ≤ next by omega), ih widths tail]

theorem sequence_validation_slices (offsets : List Nat) (scope : Nat) (data : Ssz.Bytes) :
    Refines (fun _ : Unit => (offsetWindows offsets scope).map
        (fun window => data.extract window.start window.ending))
      (unchanged 0 (validateOffsets offsets scope))
      ((Ssz.offsetSpans offsets scope).map (fun spans =>
        (offsets.zip spans).map (fun pair => data.extract pair.1 (pair.1 + pair.2)))) := by
  have validation := validateOffsets_refines offsets scope
  cases native : validateOffsets offsets scope with
  | ok value =>
    cases value
    cases pinned : Ssz.offsetSpans offsets scope with
    | error reason => simp [native, pinned, Codec.eraseResult, Except.map] at validation
    | ok spans =>
      left
      simp only [unchanged, Except.map, Codec.eraseResult]
      exact congrArg (fun slices => Except.ok (Except.ok slices))
        (sequence_offset_extracts offsets spans scope data pinned)
  | error reason =>
    left
    have mapped := congrArg (fun result => result.map (fun result => result.map
      (fun _ : Unit => (offsetWindows offsets scope).map
        (fun window => data.extract window.start window.ending)))) validation
    rw [← Codec.eraseResult_map] at mapped
    cases pinned : Ssz.offsetSpans offsets scope with
    | ok spans =>
      cases reason with
      | primitive reason => cases reason <;> simp [native, pinned, Codec.eraseResult,
          Serialize.eraseResult, Except.map] at validation
      | offsetOverflow _ | unknownSelector _ | scopeTooSmall _ _ | scopeUndivided _ _
      | scopeWidthless | firstOffset _ _ | offsetUnordered | offsetPastScope
      | offsetUnaligned | offsetBelowTable | truncated | notABit _ | paddingBits
      | emptyEncoding | noDelimiter | trailingZeros | noSelector =>
          simp [native, pinned, Codec.eraseResult, Except.map] at validation
    | error error => simpa only [Refines, unchanged, native, pinned, Except.map] using mapped

theorem decodeWindows_refines (element : Desc)
    (visit : Input → Delimited.ArenaState → Outcome Node)
    (windows : List Window) (input : Input) (allocation : Arena.Reservation)
    (index : Nat) (arena : Delimited.ArenaState)
    (physical : input.bytes.size < 2 ^ 64)
    (visitRefines : ∀ childInput childArena, childInput.bytes.size < 2 ^ 64 →
      Refines nodeErase (visit childInput childArena)
        (Ssz.deserialize element.erase childInput.bytes)) :
    Refines nodesErase (decodeWindows visit windows input allocation index arena)
      (Ssz.deserializeEach element.erase (windows.map
        (fun window => input.bytes.extract window.start window.ending))) := by
  induction windows generalizing index arena with
  | nil =>
    left
    simp only [decodeWindows, unchanged, Except.map, nodesErase, List.map_nil,
      Codec.eraseResult, Ssz.deserializeEach]
  | cons window rest ih =>
    simp only [decodeWindows, List.map_cons, Ssz.deserializeEach]
    apply refines_bind nodeErase nodesErase _ _ _ _
      (visitRefines _ _ (sequence_slice_physical input window.start window.ending physical))
    intro child used
    change Refines nodesErase
      (bind (writeValue allocation index child used) _)
      ((Ssz.deserializeEach element.erase _).bind (fun values => .ok (nodeErase child :: values)))
    apply sequence_bind_ok (fun value : Unit => value) nodesErase _ _ () _
      (Or.inl rfl)
    intro ignored nextUsed equal
    apply refines_bind nodesErase nodesErase _ _ _ _
      (ih (index + 1) { arena with used := nextUsed })
    intro children finalUsed
    exact Or.inl rfl

theorem decodeArray_refines (element : Desc)
    (visit : Input → Delimited.ArenaState → Outcome Node)
    (windows : List Window) (input : Input) (arena : Delimited.ArenaState)
    (physical : input.bytes.size < 2 ^ 64)
    (visitRefines : ∀ childInput childArena, childInput.bytes.size < 2 ^ 64 →
      Refines nodeErase (visit childInput childArena)
        (Ssz.deserialize element.erase childInput.bytes)) :
    Refines nodeErase (decodeArray visit windows input arena)
      ((Ssz.deserializeEach element.erase (windows.map
        (fun window => input.bytes.extract window.start window.ending))).map Ssz.Value.seq) := by
  have reserved : Refines (fun _ : Arena.Reservation => ())
      (reserve valueLayout windows.length arena) (.ok ()) := by
    unfold reserve
    cases TypedArena.reserve valueLayout arena.base arena.capacity arena.used windows.length with
    | none => exact Or.inr rfl
    | some allocated => exact Or.inl rfl
  unfold decodeArray
  apply sequence_bind_ok (fun _ : Arena.Reservation => ()) nodeErase _ _ () _ reserved
  intro allocated used equal
  apply refines_bind nodesErase nodeErase _ _ _ _
    (decodeWindows_refines element visit windows input allocated 0
      { arena with used := used } physical visitRefines)
  intro children finalUsed
  exact Or.inl (congrArg (fun values => Except.ok (Except.ok (Ssz.Value.seq values)))
    (node_values_erase children))

theorem decodeFixed_refines (element : Desc)
    (visit : Input → Delimited.ArenaState → Outcome Node)
    (count width : Nat) (input : Input) (arena : Delimited.ArenaState)
    (physical : input.bytes.size < 2 ^ 64)
    (visitRefines : ∀ childInput childArena, childInput.bytes.size < 2 ^ 64 →
      Refines nodeErase (visit childInput childArena)
        (Ssz.deserialize element.erase childInput.bytes)) :
    Refines nodeErase (decodeFixed visit count width input arena)
      ((Ssz.deserializeEach element.erase ((List.range count).map
        (fun index => input.bytes.extract (index * width) ((index + 1) * width)))).map Ssz.Value.seq) := by
  simpa only [decodeFixed_eq_decodeArray, fixedWindows, List.map_map, Function.comp_def,
    Nat.add_mul, Nat.one_mul] using
    decodeArray_refines element visit (fixedWindows count width) input arena physical visitRefines

theorem decodeOffsets_refines (element : Desc)
    (visit : Input → Delimited.ArenaState → Outcome Node)
    (count : Nat) (input : Input) (arena : Delimited.ArenaState)
    (physical : input.bytes.size < 2 ^ 64)
    (visitRefines : ∀ childInput childArena, childInput.bytes.size < 2 ^ 64 →
      Refines nodeErase (visit childInput childArena)
        (Ssz.deserialize element.erase childInput.bytes)) :
    Refines nodeErase (decodeOffsets visit count input arena)
      ((Ssz.offsetSpans (Ssz.readOffsets input.bytes count) input.bytes.size).bind
        (fun spans => (Ssz.deserializeEach element.erase
          (((Ssz.readOffsets input.bytes count).zip spans).map
            (fun pair => input.bytes.extract pair.1 (pair.1 + pair.2)))).map Ssz.Value.seq)) := by
  unfold decodeOffsets
  have validation := sequence_validation_slices (Ssz.readOffsets input.bytes count)
    input.bytes.size input.bytes
  have first : Refines (fun _ : Unit =>
      (offsetWindows (Ssz.readOffsets input.bytes count) input.bytes.size).map
        (fun window => input.bytes.extract window.start window.ending))
      (unchanged arena.used (validateOffsets (Ssz.readOffsets input.bytes count) input.bytes.size))
      ((Ssz.offsetSpans (Ssz.readOffsets input.bytes count) input.bytes.size).map
        (fun spans => ((Ssz.readOffsets input.bytes count).zip spans).map
          (fun pair => input.bytes.extract pair.1 (pair.1 + pair.2)))) := validation
  have composed := refines_bind _ nodeErase _
    (fun _ used => decodeArray visit
      (offsetWindows (Ssz.readOffsets input.bytes count) input.bytes.size)
      input { arena with used := used }) _
    (fun slices => (Ssz.deserializeEach element.erase slices).map Ssz.Value.seq) first
    (fun _ used => decodeArray_refines element visit _ input
      { arena with used := used } physical visitRefines)
  cases spans : Ssz.offsetSpans (Ssz.readOffsets input.bytes count) input.bytes.size <;>
    simpa only [spans, Except.map, Except.bind] using composed

end SszNative.CodecDecode

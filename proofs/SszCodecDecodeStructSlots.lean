import SszCodecDecodeStructCore

set_option autoImplicit false

namespace SszNative.CodecDecode

open Codec (Desc Error)

def entrySlot (data : Ssz.Bytes) {children : List Desc} (entry : Entry children) : Ssz.Slot :=
  match entry.slot.width with
  | some _ => .inline (data.extract entry.slot.start entry.slot.ending)
  | none => .body entry.slot.start

def entrySlots (data : Ssz.Bytes) {children : List Desc}
    (entries : List (Entry children)) : List Ssz.Slot := entries.map (entrySlot data)

def entrySlices (data : Ssz.Bytes) {children : List Desc}
    (entries : List (Entry children)) : List Ssz.Bytes :=
  entries.map fun entry => data.extract entry.slot.start entry.slot.ending

def positionedSafe {children : List Desc} (entries : List (Entry children)) (scope : Nat) : Prop :=
  ∀ entry ∈ entries, match entry.slot.width with
    | some _ => entry.slot.start ≤ entry.slot.ending ∧ entry.slot.ending ≤ scope
    | none => entry.slot.start < 2 ^ 64

/-- The header budget discharges both native conversion and checked-addition
failures. The resulting slots are exactly the pinned reader's slots. -/
theorem positionSlots_spec {children : List Desc} (entries : List (Entry children))
    (input : Input) (allocation : Arena.Reservation) (index position used : Nat)
    (physical : input.bytes.size < 2 ^ 64) (widths : widthsCorrect entries)
    (room : position + Ssz.Desc.leadingWidth (entryFields entries) ≤ input.bytes.size) :
    ∃ positioned,
      (positionSlots entries input allocation index position used).result = .ok positioned ∧
      entryDescs positioned.1 = entryDescs entries ∧
      widthsCorrect positioned.1 ∧ positionedSafe positioned.1 input.bytes.size ∧
      positioned.2 = position + Ssz.Desc.leadingWidth (entryFields entries) ∧
      Ssz.readSlots (entryFields entries) input.bytes position =
        .ok (entrySlots input.bytes positioned.1, positioned.2) := by
  induction entries generalizing index position used with
  | nil =>
    refine ⟨([], position), rfl, rfl, ?_, ?_, ?_, rfl⟩
    · simp [widthsCorrect]
    · simp [positionedSafe]
    · simp [entryFields, entryDescs, Ssz.Desc.leadingWidth]
  | cons entry rest ih =>
    have headWidth := widths entry (by simp)
    have tailWidths : widthsCorrect rest := fun next member => widths next (by simp [member])
    let width := (entry.slot.width.map NatOperand.value).getD 4
    let ending := position + width
    let slot : Slot := match entry.slot.width with
      | some _ => { entry.slot with start := position, ending := ending }
      | none => { entry.slot with start := Ssz.readUint input.bytes position 4 }
    have widthValue : width = entry.desc.erase.fixedSize.getD 4 := by
      simp only [width, headWidth]
    have leading : Ssz.Desc.leadingWidth (entryFields (entry :: rest)) =
        width + Ssz.Desc.leadingWidth (entryFields rest) := by
      simp only [entryFields, entryDescs, List.map_cons, Ssz.Desc.leadingWidth,
        Ssz.bytesPerOffset, widthValue]
    have nextRoom : ending + Ssz.Desc.leadingWidth (entryFields rest) ≤ input.bytes.size := by
      rw [leading] at room
      dsimp [ending]
      omega
    have endBound : ending ≤ input.bytes.size := by omega
    have fits : width < 2 ^ 64 := by dsimp [ending] at endBound; omega
    have guard : ¬ (2 ^ 64 ≤ ending ∨ input.bytes.size < ending) := by omega
    obtain ⟨result, run, descs, correct, safe, finish, read⟩ :=
      ih (index + 1) ending used tailWidths nextRoom
    refine ⟨({ entry with slot := slot } :: result.1, result.2), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cases nativeWidth : entry.slot.width with
      | none =>
        have widthFour : width = 4 := by
          simp only [width, nativeWidth, Option.map_none, Option.getD_none]
        have guardFour : ¬ (2 ^ 64 ≤ position + 4 ∨ input.bytes.size < position + 4) := by
          simpa only [ending, widthFour] using guard
        have runFour : (positionSlots rest input allocation (index + 1) (position + 4) used).result =
            .ok result := by
          simpa only [ending, widthFour] using run
        simp only [positionSlots, nativeWidth, bind, unchanged, guardFour, ↓reduceIte,
          writeSlot, runFour, slot]
      | some number =>
        have widthNumber : width = number.value := by
          simp only [width, nativeWidth, Option.map_some, Option.getD_some]
        have numberFits : number.value < 2 ^ 64 := by
          simpa only [widthNumber] using fits
        have guardNumber : ¬ (2 ^ 64 ≤ position + number.value ∨
            input.bytes.size < position + number.value) := by
          simpa only [ending, widthNumber] using guard
        have runNumber :
            (positionSlots rest input allocation (index + 1) (position + number.value) used).result =
              .ok result := by
          simpa only [ending, widthNumber] using run
        simp only [positionSlots, nativeWidth, narrow, numberFits, ↓reduceIte, bind,
          unchanged, guardNumber, writeSlot, runNumber, slot, ending, widthNumber]
    · simpa only [entryDescs, List.map_cons] using congrArg (entry.desc :: ·) descs
    · intro next member
      rcases List.mem_cons.mp member with same | member
      · subst next
        cases nativeWidth : entry.slot.width <;>
          simpa only [slot, nativeWidth] using headWidth
      · exact correct next member
    · intro next member
      rcases List.mem_cons.mp member with same | member
      · subst next
        cases nativeWidth : entry.slot.width with
        | none =>
          have bound := WordDecode.readUint_lt input.bytes position 4
          simp only [slot, nativeWidth]
          omega
        | some number =>
          simp only [slot, nativeWidth]
          exact ⟨by dsimp [ending]; omega, endBound⟩
      · exact safe next member
    · rw [finish, leading]
      dsimp [ending]
      omega
    · cases nativeWidth : entry.slot.width with
      | none =>
        have fixed : entry.desc.erase.fixedSize = none := by
          simpa only [nativeWidth, Option.map_none] using headWidth.symm
        have widthFour : width = 4 := by simp [width, nativeWidth]
        have bound : ¬ input.bytes.size < position + 4 := by
          dsimp [ending] at endBound
          omega
        have tailRead : Ssz.readSlots (entryFields rest) input.bytes (position + 4) =
            .ok (entrySlots input.bytes result.1, result.2) := by
          simpa only [ending, widthFour] using read
        change Ssz.readSlots (entry.desc.erase :: entryFields rest) input.bytes position = _
        simp only [Ssz.readSlots, fixed, Ssz.bytesPerOffset, bound, ↓reduceIte,
          Bind.bind, Except.bind, tailRead, Pure.pure, Except.pure,
          entrySlots, List.map_cons, entrySlot, slot, nativeWidth]
      | some number =>
        have fixed : entry.desc.erase.fixedSize = some number.value := by
          simpa only [nativeWidth, Option.map_some] using headWidth.symm
        have widthNumber : width = number.value := by simp [width, nativeWidth]
        have bound : ¬ input.bytes.size < position + number.value := by
          dsimp [ending] at endBound
          omega
        have tailRead : Ssz.readSlots (entryFields rest) input.bytes (position + number.value) =
            .ok (entrySlots input.bytes result.1, result.2) := by
          simpa only [ending, widthNumber] using read
        change Ssz.readSlots (entry.desc.erase :: entryFields rest) input.bytes position = _
        simp only [Ssz.readSlots, fixed, bound, ↓reduceIte, Bind.bind, Except.bind,
          tailRead, Pure.pure, Except.pure, entrySlots, List.map_cons, entrySlot,
          slot, nativeWidth, ending, widthNumber]

theorem nextBody_eq {children : List Desc} (entries : List (Entry children))
    (data : Ssz.Bytes) (scope : Nat) :
    nextBody entries scope = (Ssz.bodyStarts (entrySlots data entries)).headD scope := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    cases width : entry.slot.width <;>
      simp only [nextBody, Option.isSome, Bool.false_eq_true, ↓reduceIte,
        entrySlots, List.map_cons, entrySlot, width, Ssz.bodyStarts, List.headD_cons,
        ih]

theorem closeSlots_length {children : List Desc} (entries : List (Entry children)) (scope : Nat) :
    (closeSlots entries scope).length = entries.length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih => simp only [closeSlots, List.length_cons, ih]

/-- A successful span head is the exact next boundary, including empty bodies. -/
theorem struct_offsetSpans_cons (start : Nat) (rest : List Nat) (scope : Nat)
    (spans : List Nat) (read : Ssz.offsetSpans (start :: rest) scope = .ok spans) :
    ∃ width widths, spans = width :: widths ∧
      start ≤ rest.headD scope ∧ rest.headD scope ≤ scope ∧
      start + width = rest.headD scope ∧ Ssz.offsetSpans rest scope = .ok widths := by
  induction rest generalizing start spans with
  | nil =>
    simp only [Ssz.offsetSpans] at read
    split at read
    · cases read
    · have equal := Except.ok.inj read
      subst spans
      refine ⟨scope - start, [], rfl, ?_, by simp, ?_, rfl⟩ <;> simp_all <;> omega
  | cons next rest ih =>
    simp only [Ssz.offsetSpans] at read
    split at read
    · cases read
    · rename_i ordered
      cases tail : Ssz.offsetSpans (next :: rest) scope with
      | error reason => simp [tail, Bind.bind, Except.bind] at read
      | ok widths =>
        simp only [tail, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] at read
        subst spans
        obtain ⟨width, remaining, _, onward, within, _, _⟩ := ih next widths tail
        refine ⟨next - start, widths, rfl, ?_, ?_, ?_, rfl⟩ <;> simp only [List.headD_cons] <;> omega

/-- The pure readback closes exactly the same intervals as the accepted offset
span algorithm, without subtractive underflow or clipping an invalid boundary. -/
theorem closeSlots_takeSlots {children : List Desc} (entries : List (Entry children))
    (data : Ssz.Bytes) (spans : List Nat)
    (read : Ssz.offsetSpans (Ssz.bodyStarts (entrySlots data entries)) data.size = .ok spans) :
    Ssz.takeSlots data (entrySlots data entries) spans =
      .ok (entrySlices data (closeSlots entries data.size)) := by
  induction entries generalizing spans with
  | nil => rfl
  | cons entry rest ih =>
    cases width : entry.slot.width with
    | some number =>
      have tailRead : Ssz.offsetSpans (Ssz.bodyStarts (entrySlots data rest)) data.size = .ok spans := by
        simpa only [entrySlots, List.map_cons, entrySlot, width, Ssz.bodyStarts] using read
      have tailTaken := ih spans tailRead
      simp only [entrySlots, entrySlices] at tailTaken
      simp only [entrySlots, List.map_cons, entrySlot, Ssz.takeSlots,
        tailTaken, Bind.bind, Except.bind, Pure.pure, Except.pure,
        closeSlots, width, Option.isSome, ↓reduceIte, entrySlices]
    | none =>
      have spansRead : Ssz.offsetSpans
          (entry.slot.start :: Ssz.bodyStarts (entrySlots data rest)) data.size = .ok spans := by
        simpa only [entrySlots, List.map_cons, entrySlot, width, Ssz.bodyStarts] using read
      obtain ⟨span, remaining, rfl, _, _, ending, tailRead⟩ :=
        struct_offsetSpans_cons entry.slot.start _ data.size spans spansRead
      rw [← nextBody_eq rest data data.size] at ending
      have tailTaken := ih remaining tailRead
      simp only [entrySlots, entrySlices] at tailTaken
      simp only [entrySlots, List.map_cons, entrySlot, Ssz.takeSlots,
        tailTaken, Bind.bind, Except.bind, Pure.pure, Except.pure,
        closeSlots, width, Option.isSome, Bool.false_eq_true, ↓reduceIte,
        entrySlices, ending]

theorem closeSlots_safe {children : List Desc} (entries : List (Entry children))
    (data : Ssz.Bytes) (spans : List Nat) (safe : positionedSafe entries data.size)
    (read : Ssz.offsetSpans (Ssz.bodyStarts (entrySlots data entries)) data.size = .ok spans) :
    ∀ entry ∈ closeSlots entries data.size,
      entry.slot.start ≤ entry.slot.ending ∧ entry.slot.ending ≤ data.size := by
  induction entries generalizing spans with
  | nil => simp [closeSlots]
  | cons entry rest ih =>
    have restSafe : positionedSafe rest data.size := fun next member => safe next (by simp [member])
    cases width : entry.slot.width with
    | some number =>
      have tailRead : Ssz.offsetSpans (Ssz.bodyStarts (entrySlots data rest)) data.size = .ok spans := by
        simpa only [entrySlots, List.map_cons, entrySlot, width, Ssz.bodyStarts] using read
      intro next member
      simp only [closeSlots, width, Option.isSome, ↓reduceIte, List.mem_cons] at member
      rcases member with rfl | member
      · simpa only [width] using safe entry (by simp)
      · exact ih spans restSafe tailRead next member
    | none =>
      have spansRead : Ssz.offsetSpans
          (entry.slot.start :: Ssz.bodyStarts (entrySlots data rest)) data.size = .ok spans := by
        simpa only [entrySlots, List.map_cons, entrySlot, width, Ssz.bodyStarts] using read
      obtain ⟨span, remaining, _, onward, within, _, tailRead⟩ :=
        struct_offsetSpans_cons entry.slot.start _ data.size spans spansRead
      rw [← nextBody_eq rest data data.size] at onward within
      intro next member
      simp only [closeSlots, width, Option.isSome, Bool.false_eq_true, ↓reduceIte,
        List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨onward, within⟩
      · exact ih remaining restSafe tailRead next member

theorem positionSlots_descs_success {children : List Desc} (entries : List (Entry children))
    (input : Input) (allocation : Arena.Reservation) (index position used : Nat)
    (positioned : List (Entry children) × Nat)
    (success : (positionSlots entries input allocation index position used).result = .ok positioned) :
    entryDescs positioned.1 = entryDescs entries := by
  induction entries generalizing index position used positioned with
  | nil =>
    simp only [positionSlots, unchanged, Except.ok.injEq] at success
    subst positioned
    rfl
  | cons entry rest ih =>
    simp only [positionSlots] at success
    obtain ⟨width, _, success⟩ := struct_bind_success _ _ _ success
    split at success
    · cases success
    · obtain ⟨written, _, success⟩ := struct_bind_success _ _ _ success
      obtain ⟨remaining, tailRun, success⟩ := struct_bind_success _ _ _ success
      simp only [unchanged, Except.ok.injEq] at success
      subst positioned
      simpa only [entryDescs, List.map_cons] using
        congrArg (entry.desc :: ·) (ih (index + 1) _ _ remaining tailRun)

theorem positionSlots_length_success {children : List Desc} (entries : List (Entry children))
    (input : Input) (allocation : Arena.Reservation) (index position used : Nat)
    (positioned : List (Entry children) × Nat)
    (success : (positionSlots entries input allocation index position used).result = .ok positioned) :
    positioned.1.length = entries.length := by
  have lengths := congrArg List.length
    (positionSlots_descs_success entries input allocation index position used positioned success)
  simpa only [entryDescs, List.length_map] using lengths

end SszNative.CodecDecode

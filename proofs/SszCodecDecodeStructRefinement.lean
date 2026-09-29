import SszCodecDecodeStructValidation

set_option autoImplicit false

namespace SszNative.CodecDecode

open Codec (Desc Error)

private theorem struct_bind_pure {α β : Type} (used : Nat) (value : α)
    (next : α → Nat → Outcome β) :
    bind (unchanged used (.ok value)) next = next value used := by
  simp only [bind, unchanged, List.nil_append]

private theorem struct_bind_error {α β : Type} (used : Nat) (reason : Error)
    (next : α → Nat → Outcome β) :
    bind (unchanged used (.error reason)) next = unchanged used (.error reason) := rfl

private theorem struct_refines_return {α β γ : Type} (erase : β → γ)
    (first : Outcome α) (next : α → Nat → Outcome β) (value : α)
    (expected : Except Ssz.Err γ) (returned : first.result = .ok value)
    (continues : Refines erase (next value first.used) expected) :
    Refines erase (bind first next) expected := by
  simpa only [Refines, bind, returned] using continues

private theorem struct_refinement_throw {α : Type} (reason : Ssz.Err) :
    (throw reason : Except Ssz.Err α) = .error reason := rfl

attribute [local simp] struct_refinement_throw
attribute [local simp] Bind.bind Pure.pure Functor.map Except.pure Except.bind Except.map Except.mapError

theorem struct_except_bind_assoc {α β γ : Type} (first : Except Ssz.Err α)
    (next : α → Except Ssz.Err β) (last : β → Except Ssz.Err γ) :
    (first.bind next).bind last = first.bind (fun value => (next value).bind last) := by
  cases first <;> rfl

/-- A continuation may use the already-returned semantic success, not a
hypothesis about any future execution. -/
theorem struct_refines_bind_success {α β γ δ : Type} (eraseFirst : α → γ) (eraseNext : β → δ)
    (first : Outcome α) (next : α → Nat → Outcome β)
    (expected : Except Ssz.Err γ) (continuation : γ → Except Ssz.Err δ)
    (firstRefines : Refines eraseFirst first expected)
    (nextRefines : ∀ value used, expected = .ok (eraseFirst value) →
      Refines eraseNext (next value used) (continuation (eraseFirst value))) :
    Refines eraseNext (bind first next) (expected.bind continuation) := by
  cases result : first.result with
  | error reason =>
    have dummy := refines_bind eraseFirst eraseNext first
      (fun _ used => unchanged used (.error scratch)) expected continuation firstRefines
      (fun _ _ => Or.inr rfl)
    simpa only [Refines, bind, result] using dummy
  | ok value =>
    rcases firstRefines with correct | exhausted
    · have equal : expected = .ok (eraseFirst value) := by
        symm
        simpa only [result, Except.map, Codec.eraseResult, Except.ok.injEq] using correct
      simpa only [Refines, bind, result, equal, Except.bind] using
        nextRefines value first.used equal
    · simp only [result] at exhausted
      cases exhausted

/-- Field and byte lists are produced from the very same entries, so arity is
preserved without a declaration-validity or future-decode premise. -/
theorem decodeEntries_refines {children : List Desc} (entries : List (Entry children))
    (visit : Visit children) (input : Input) (allocation : Arena.Reservation)
    (index : Nat) (arena : Delimited.ArenaState) (physical : input.bytes.size < 2 ^ 64)
    (visits : ∀ child member childInput childArena, childInput.bytes.size < 2 ^ 64 →
      Refines nodeErase (visit child member childInput childArena)
        (Ssz.deserialize child.erase childInput.bytes)) :
    Refines nodesErase (decodeEntries entries visit input allocation index arena)
      (Ssz.deserializeFields (entryFields entries) (entrySlices input.bytes entries)) := by
  induction entries generalizing index arena with
  | nil =>
    left
    simp only [decodeEntries, unchanged, Except.map, nodesErase, List.map_nil,
      Codec.eraseResult, Ssz.deserializeFields, entryFields, entryDescs, entrySlices]
  | cons entry rest ih =>
    have slicePhysical : (input.slice entry.slot.start entry.slot.ending).bytes.size < 2 ^ 64 := by
      simp only [Input.slice, Array.size_extract]
      omega
    simp only [decodeEntries, entryFields, entryDescs, entrySlices, List.map_cons,
      Ssz.deserializeFields, Bind.bind, Except.bind, Pure.pure, Except.pure]
    apply refines_bind nodeErase nodesErase _ _ _ _
      (visits entry.desc entry.member (input.slice entry.slot.start entry.slot.ending) arena slicePhysical)
    intro child used
    apply structSpec_refines_bind _ _ (fun _ : Unit => True) _ _
      (show StructSpec (writeValue allocation index child used) (fun _ => True) from True.intro)
    intro _ used _
    apply refines_bind nodesErase nodesErase _ _ _ _
      (ih (index + 1) { arena with used := used })
    intro decoded used
    exact Or.inl rfl

theorem decodeEntries_arity {children : List Desc} (entries : List (Entry children))
    (visit : Visit children) (input : Input) (allocation : Arena.Reservation)
    (index : Nat) (arena : Delimited.ArenaState) (decoded : List Node)
    (success : (decodeEntries entries visit input allocation index arena).result = .ok decoded) :
    decoded.length = entries.length := by
  induction entries generalizing index arena decoded with
  | nil =>
    simp only [decodeEntries, unchanged, Except.ok.injEq] at success
    subst decoded
    rfl
  | cons entry rest ih =>
    simp only [decodeEntries] at success
    obtain ⟨child, _, success⟩ := struct_bind_success _ _ _ success
    obtain ⟨written, _, success⟩ := struct_bind_success _ _ _ success
    obtain ⟨remaining, remainingResult, success⟩ := struct_bind_success _ _ _ success
    simp only [unchanged, Except.ok.injEq] at success
    subst decoded
    simp only [List.length_cons]
    congr 1
    exact ih (index + 1) _ remaining remainingResult

theorem measuredBudget_refines {children : List Desc} (measured : Measured children)
    (fields : List Ssz.Desc) (input : Input) (used : Nat)
    (physical : input.bytes.size < 2 ^ 64)
    (leading : measured.leading.value = Ssz.Desc.leadingWidth fields)
    (fixed : measured.allFixed = (Ssz.Desc.fieldsFixedSize fields).isSome) :
    Refines (fun value : Unit => value)
      (if measured.allFixed then exact measured.leading input.bytes.size used
       else if input.bytes.size < measured.leading.value then
         unchanged used (.error (.scopeTooSmall measured.leading (Serialize.count input.bytes.size)))
       else unchanged used (.ok ()))
      (Ssz.structBudget fields input.bytes.size) := by
  cases width : Ssz.Desc.fieldsFixedSize fields with
  | none =>
    have isVariable : measured.allFixed = false := by simpa only [width, Option.isSome_none] using fixed
    by_cases short : input.bytes.size < Ssz.Desc.leadingWidth fields <;>
      simp [Refines, isVariable, leading, short, Ssz.structBudget, width, unchanged,
        Codec.eraseResult, count_value input.bytes.size physical]
  | some size =>
    have allFixed : measured.allFixed = true := by simpa only [width, Option.isSome_some] using fixed
    have value : measured.leading.value = size := leading.trans (fieldsFixedSize_leading fields size width)
    by_cases same : size = input.bytes.size
    · simp [Refines, allFixed, exact, Ssz.structBudget, width, value, same,
        unchanged, Codec.eraseResult]
    · have reverse : input.bytes.size ≠ size := Ne.symm same
      simp [Refines, allFixed, exact, Ssz.structBudget, width, value, same, reverse,
        unchanged, Codec.eraseResult, Serialize.eraseResult,
        count_value input.bytes.size physical]

theorem structBudget_room (fields : List Ssz.Desc) (scope : Nat)
    (success : Ssz.structBudget fields scope = .ok ()) :
    Ssz.Desc.leadingWidth fields ≤ scope := by
  cases fixed : Ssz.Desc.fieldsFixedSize fields with
  | none =>
    simp only [Ssz.structBudget, fixed] at success
    split at success
    · cases success
    · omega
  | some width =>
    have leading := fieldsFixedSize_leading fields width fixed
    simp only [Ssz.structBudget, fixed] at success
    split at success
    · cases success
    · simp_all

/-- Native structure decoding refines both pinned container forms for arbitrary
raw logical declarations. The only alternative is actual scratch exhaustion. -/
theorem structureValue_refines (children : List Desc) (visit : Visit children)
    (input : Input) (arena : Delimited.ArenaState) (physical : input.bytes.size < 2 ^ 64)
    (visits : ∀ child member childInput childArena, childInput.bytes.size < 2 ^ 64 →
      Refines nodeErase (visit child member childInput childArena)
        (Ssz.deserialize child.erase childInput.bytes)) :
    Refines nodeErase (structureValue children visit input arena)
      ((Ssz.structSlices (children.map Desc.erase) input.bytes).bind fun slices =>
        (Ssz.deserializeFields (children.map Desc.erase) slices).map Ssz.Value.seq) := by
  unfold structureValue
  by_cases overflow : 2 ^ 32 ≤ input.bytes.size
  · simp only [compositeSize, overflow, ↓reduceIte, struct_bind_error]
    left
    simp [unchanged, Codec.eraseResult, count_value input.bytes.size physical,
      Ssz.structSlices, Ssz.bytesPerOffset, overflow]
  · have small : input.bytes.size < 2 ^ 32 := by omega
    simp only [compositeSize, overflow, ↓reduceIte, struct_bind_pure]
    apply structSpec_refines_bind _ _ _ _ _
      (structSpec_reserve slotLayout children.length arena)
    intro slots used _
    apply structSpec_refines_bind _ _ (fun _ : Unit => True) _ _
      (show StructSpec (initializeSlots children.length slots used) (fun _ => True) from True.intro)
    intro _ used _
    apply structSpec_refines_bind _ _ _ _ _
      (measureSlots_spec (initialEntries children) slots 0 (.small 0) true { arena with used := used })
    intro measured used valid
    rcases valid with ⟨descs, widths, leading, fixed⟩
    have initial : entryFields (initialEntries children) = children.map Desc.erase := by
      rw [entryFields, initialEntries_descs]
    have fields : entryFields measured.entries = children.map Desc.erase := by
      rw [entryFields, descs, initialEntries_descs]
    have leadingValue : measured.leading.value = Ssz.Desc.leadingWidth (children.map Desc.erase) := by
      simpa only [initial, FixedSize.small_zero_value, Nat.zero_add] using leading
    have allFixed : measured.allFixed = (Ssz.Desc.fieldsFixedSize (children.map Desc.erase)).isSome := by
      simpa only [initial, Bool.true_and] using fixed
    rw [structSlices_eq _ _ small]
    simp only [struct_except_bind_assoc]
    apply struct_refines_bind_success (fun value : Unit => value) nodeErase _ _ _ _
      (measuredBudget_refines measured (children.map Desc.erase) input used physical leadingValue allFixed)
    intro checked used budget
    cases checked
    have room := structBudget_room (children.map Desc.erase) input.bytes.size budget
    obtain ⟨positioned, positionedRun, positionedDescs, positionedWidths, safe, ending, read⟩ :=
      positionSlots_spec measured.entries input slots 0 0 used physical widths
        (by simpa only [fields, Nat.zero_add] using room)
    have positionedFields : entryFields positioned.1 = children.map Desc.erase := by
      rw [entryFields, positionedDescs]
      exact fields
    have front : positioned.2 < 2 ^ 64 := by
      rw [ending, fields, Nat.zero_add]
      omega
    have readFields : Ssz.readSlots (children.map Desc.erase) input.bytes 0 =
        .ok (entrySlots input.bytes positioned.1, positioned.2) := by
      simpa only [fields] using read
    rw [readFields]
    change Refines nodeErase (bind _ _)
      ((structFinish (entrySlots input.bytes positioned.1) positioned.2 input.bytes).bind fun slices =>
        (Ssz.deserializeFields (children.map Desc.erase) slices).map Ssz.Value.seq)
    apply struct_refines_return nodeErase _ _ positioned _ positionedRun
    apply refines_bind (fun _ : Unit => entrySlices input.bytes (closeSlots positioned.1 input.bytes.size))
      nodeErase _ _ _ _
      (validateSlots_finish_refines positioned.1 input.bytes slots 0 positioned.2 _ physical front safe)
    intro _ used
    apply structSpec_refines_bind _ _ _ _ _
      (structSpec_reserve valueLayout children.length { arena with used := used })
    intro values used _
    have closedFields : entryFields (closeSlots positioned.1 input.bytes.size) = children.map Desc.erase := by
      rw [entryFields, closeSlots_descs]
      exact positionedFields
    have decoded := decodeEntries_refines (closeSlots positioned.1 input.bytes.size) visit input values 0
      { arena with used := used } physical visits
    rw [closedFields] at decoded
    change Refines nodeErase (bind _ _) ((Ssz.deserializeFields _ _).map Ssz.Value.seq)
    apply refines_bind nodesErase nodeErase _ _ _ _ decoded
    intro decoded used
    exact Or.inl (congrArg (fun values => Except.ok (Except.ok (Ssz.Value.seq values)))
      (node_values_erase decoded))

end SszNative.CodecDecode

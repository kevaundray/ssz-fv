import SszHashLayoutDomain

set_option autoImplicit false

namespace SszNative.HashLayout

open Codec (Desc Value)
/-- The outer leaf guard agrees with the optional view on every raw input. -/
theorem Nested.at_none_of_count_le (nested : Nested) (index : Nat)
    (outside : nested.count ≤ index) : nested.at index = none := by
  cases nested with
  | sequence element values =>
    simp only [Nested.count] at outside
    simp [Nested.at, List.getElem?_eq_none outside]
  | fields fields values =>
    simp only [Nested.count] at outside
    simp only [Nested.at, List.getElem?_eq_none outside, Option.map_none]
    cases fields[index]? <;> rfl
  | progressive active fields values =>
    simp only [Nested.count] at outside
    simp [Nested.at, List.getElem?_eq_none outside]
  | union desc value =>
    have nonzero : index ≠ 0 := by simp only [Nested.count] at outside; omega
    simp [Nested.at, nonzero]


def erasePair (pair : Desc × Value) : Ssz.Desc × Ssz.Value :=
  (pair.1.erase, pair.2.erase)

/-- Numerical first-match lookup agrees even with duplicates and padded operands.
In particular there is no premature selector-range rejection. -/
theorem lookup_refines (variants : List (NatOperand × Desc)) (selector : NatOperand) :
    Ssz.lookupOption (variants.map (fun variant => variant.1.value))
      (Desc.eraseVariants variants) selector.value =
      match lookup variants selector with
      | none => .error (.unknownSelector selector.value)
      | some desc => .ok desc.erase := by
  induction variants with
  | nil => rfl
  | cons variant rest ih =>
    rcases variant with ⟨chosen, desc⟩
    by_cases same : chosen.value = selector.value
    · simp [lookup, Ssz.lookupOption, Desc.eraseVariants, same]
    · simp [lookup, Ssz.lookupOption, Desc.eraseVariants, same, ih]

@[simp] theorem lookup_first (chosen selector : NatOperand) (desc : Desc)
    (rest : List (NatOperand × Desc)) (same : chosen.value = selector.value) :
    lookup ((chosen, desc) :: rest) selector = some desc := by
  simp [lookup, same]

theorem lookup_skip (chosen selector : NatOperand) (desc : Desc)
    (rest : List (NatOperand × Desc)) (different : chosen.value ≠ selector.value) :
    lookup ((chosen, desc) :: rest) selector = lookup rest selector := by
  simp [lookup, different]

/-- The native independent optional field/value reads refine paired indexing,
including malformed unequal-length inputs. -/
theorem Nested.fields_at_zip (fields : List (String × Desc)) (values : List Value)
    (index : Nat) :
    ((Nested.fields fields values).at index).map erasePair =
      ((Desc.eraseFields fields).zip (Value.eraseList values))[index]? := by
  simp only [Nested.at, Desc.eraseFields_eq_map, Value.eraseList_eq_map,
    List.zip, List.getElem?_zipWith, List.getElem?_map]
  cases fields[index]? <;> cases values[index]? <;> rfl

theorem Nested.sequence_at (element : Desc) (values : List Value) (index : Nat) :
    ((Nested.sequence element values).at index).map erasePair =
      ((Value.eraseList values).map (fun value => some (element.erase, value)))[index]?.getD none := by
  simp only [Nested.at, Value.eraseList_eq_map, List.getElem?_map]
  cases values[index]? <;> rfl

theorem Nested.fields_at (fields : List (String × Desc)) (values : List Value)
    (index : Nat) :
    ((Nested.fields fields values).at index).map erasePair =
      (((Desc.eraseFields fields).zip (Value.eraseList values)).map some)[index]?.getD none := by
  rw [Nested.fields_at_zip]
  simp only [List.getElem?_map]
  cases ((Desc.eraseFields fields).zip (Value.eraseList values))[index]? <;> rfl

theorem Nested.union_at (desc : Desc) (value : Value) (index : Nat) :
    ((Nested.union desc value).at index).map erasePair =
      [some (desc.erase, value.erase)][index]?.getD none := by
  cases index <;> simp [Nested.at, erasePair]

/-- Every successful placement has exactly the native ordinal read at each index.
The statement includes indices outside the layout and all inactive gaps. -/
theorem placeSlots_at {active : List Bool} {fields : List (Ssz.Desc × Ssz.Value)}
    {slots : List (Option (Ssz.Desc × Ssz.Value))}
    (placed : Ssz.placeSlots active fields = .ok slots) (index : Nat) :
    slots[index]?.getD none =
      if active[index]?.getD false then fields[(active.take index).countP id]? else none := by
  induction active generalizing fields slots index with
  | nil =>
    cases fields with
    | nil =>
      have same : slots = [] := by simpa [Ssz.placeSlots] using placed.symm
      subst slots
      simp
    | cons field rest => simp [Ssz.placeSlots] at placed
  | cons bit active ih =>
    cases bit with
    | false =>
      cases h : Ssz.placeSlots active fields with
      | error reason => simp [Ssz.placeSlots, h, Bind.bind, Except.bind] at placed
      | ok rest =>
        have same : none :: rest = slots := by
          simpa [Ssz.placeSlots, h, Bind.bind, Except.bind, pure, Except.pure] using placed
        subst slots
        cases index with
        | zero => simp
        | succ index => simpa using ih h index
    | true =>
      cases fields with
      | nil => simp [Ssz.placeSlots] at placed
      | cons field fields =>
        cases h : Ssz.placeSlots active fields with
        | error reason => simp [Ssz.placeSlots, h, Bind.bind, Except.bind] at placed
        | ok rest =>
          have same : some field :: rest = slots := by
            simpa [Ssz.placeSlots, h, Bind.bind, Except.bind, pure, Except.pure] using placed
          subst slots
          cases index with
          | zero => simp
          | succ index => simpa [Nat.add_comm] using ih h index

theorem placeSlots_exists (active : List Bool) (fields : List (Ssz.Desc × Ssz.Value))
    (counted : active.countP id = fields.length) :
    ∃ slots, Ssz.placeSlots active fields = .ok slots := by
  induction active generalizing fields with
  | nil =>
    have empty : fields = [] := List.eq_nil_of_length_eq_zero (by simpa using counted.symm)
    subst fields
    exact ⟨[], rfl⟩
  | cons bit active ih =>
    cases bit with
    | false =>
      obtain ⟨slots, placed⟩ := ih fields (by simpa using counted)
      exact ⟨none :: slots, by simp [Ssz.placeSlots, placed, Bind.bind, Except.bind, pure, Except.pure]⟩
    | true =>
      cases fields with
      | nil => simp at counted
      | cons field fields =>
        obtain ⟨slots, placed⟩ := ih fields (by simpa using counted)
        exact ⟨some field :: slots, by
          simp [Ssz.placeSlots, placed, Bind.bind, Except.bind, pure, Except.pure]⟩

/-- Arity is checked before the number of active positions. -/
theorem layoutSlots_arity_error (active : List Bool) (fields : List (String × Desc))
    (values : List Value) (arity : fields.length ≠ values.length) :
    Ssz.layoutSlots active (Desc.eraseFields fields) (Value.eraseList values) =
      .error .typeMismatch := by
  simp [Ssz.layoutSlots, arity, Bind.bind, Except.bind]
  rfl

theorem layoutSlots_count_error (active : List Bool) (fields : List (String × Desc))
    (values : List Value) (arity : fields.length = values.length)
    (counted : active.countP id ≠ fields.length) :
    Ssz.layoutSlots active (Desc.eraseFields fields) (Value.eraseList values) =
      .error (.layoutFieldCount (active.countP id) fields.length) := by
  simp [Ssz.layoutSlots, ← arity, counted, Bind.bind, Except.bind]
  rfl

theorem layoutSlots_success (active : List Bool) (fields : List (String × Desc))
    (values : List Value) (arity : fields.length = values.length)
    (counted : active.countP id = fields.length) :
    ∃ slots, Ssz.layoutSlots active (Desc.eraseFields fields) (Value.eraseList values) =
      .ok slots := by
  obtain ⟨slots, placed⟩ := placeSlots_exists active
    ((Desc.eraseFields fields).zip (Value.eraseList values)) (by simp [counted, arity])
  exact ⟨slots, by simp [Ssz.layoutSlots, counted, arity, placed] <;> rfl⟩

theorem layoutSlots_placed {active : List Bool} {fields : List (String × Desc)}
    {values : List Value} {slots : List (Option (Ssz.Desc × Ssz.Value))}
    (placed : Ssz.layoutSlots active (Desc.eraseFields fields) (Value.eraseList values) =
      .ok slots) :
    Ssz.placeSlots active ((Desc.eraseFields fields).zip (Value.eraseList values)) = .ok slots := by
  by_cases arity : fields.length = values.length
  · by_cases counted : active.countP id = fields.length
    · have sourceEq : Ssz.layoutSlots active (Desc.eraseFields fields) (Value.eraseList values) =
          Ssz.placeSlots active ((Desc.eraseFields fields).zip (Value.eraseList values)) := by
        simp [Ssz.layoutSlots, arity, counted] <;> rfl
      rw [sourceEq] at placed
      exact placed
    · rw [layoutSlots_count_error active fields values arity counted] at placed
      cases placed
  · rw [layoutSlots_arity_error active fields values arity] at placed
    cases placed

theorem Nested.progressive_at {active : List Bool} {fields : List (String × Desc)}
    {values : List Value} {slots : List (Option (Ssz.Desc × Ssz.Value))}
    (placed : Ssz.layoutSlots active (Desc.eraseFields fields) (Value.eraseList values) =
      .ok slots) (index : Nat) :
    ((Nested.progressive active fields values).at index).map erasePair =
      slots[index]?.getD none := by
  rw [placeSlots_at (layoutSlots_placed placed) index]
  simp only [Nested.at]
  split
  · exact Nested.fields_at_zip fields values _
  · rfl

theorem Nested.sequence_count (element : Desc) (values : List Value) :
    (Nested.sequence element values).count =
      ((Value.eraseList values).map (fun value => some (element.erase, value))).length := by
  simp [Nested.count]

theorem Nested.fields_count (fields : List (String × Desc)) (values : List Value)
    (arity : fields.length = values.length) :
    (Nested.fields fields values).count =
      (((Desc.eraseFields fields).zip (Value.eraseList values)).map some).length := by
  simp [Nested.count, arity]

/-- Local placement length law, independent of the vendor Merkle proof stack. -/
theorem placeSlots_length {active : List Bool} {fields : List (Ssz.Desc × Ssz.Value)}
    {slots : List (Option (Ssz.Desc × Ssz.Value))}
    (placed : Ssz.placeSlots active fields = .ok slots) : slots.length = active.length := by
  induction active generalizing fields slots with
  | nil =>
    cases fields with
    | nil =>
      have same : slots = [] := by simpa [Ssz.placeSlots] using placed.symm
      subst slots
      rfl
    | cons field rest => simp [Ssz.placeSlots] at placed
  | cons bit active ih =>
    cases bit with
    | false =>
      cases h : Ssz.placeSlots active fields with
      | error reason => simp [Ssz.placeSlots, h, Bind.bind, Except.bind] at placed
      | ok rest =>
        have same : none :: rest = slots := by
          simpa [Ssz.placeSlots, h, Bind.bind, Except.bind, pure, Except.pure] using placed
        subst slots
        simpa using ih h
    | true =>
      cases fields with
      | nil => simp [Ssz.placeSlots] at placed
      | cons field fields =>
        cases h : Ssz.placeSlots active fields with
        | error reason => simp [Ssz.placeSlots, h, Bind.bind, Except.bind] at placed
        | ok rest =>
          have same : some field :: rest = slots := by
            simpa [Ssz.placeSlots, h, Bind.bind, Except.bind, pure, Except.pure] using placed
          subst slots
          simpa using ih h

theorem Nested.progressive_count {active : List Bool} {fields : List (String × Desc)}
    {values : List Value} {slots : List (Option (Ssz.Desc × Ssz.Value))}
    (placed : Ssz.layoutSlots active (Desc.eraseFields fields) (Value.eraseList values) =
      .ok slots) : (Nested.progressive active fields values).count = slots.length := by
  exact (placeSlots_length (layoutSlots_placed placed)).symm

end SszNative.HashLayout

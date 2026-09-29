import SszCodecMeasure
import SszFixedSizeClassification
import SszSerializeMeasure
import Ssz.Proofs.Codec.Table

set_option autoImplicit false

namespace SszNative.CodecMeasure

open Codec (Desc Value)

abbrev ExpectedVisit (values : List Value) :=
  (value : Value) → value ∈ values → Desc → Except Ssz.Err Nat

/-- Accumulate the paired prefix. Arity is checked only after every paired child. -/
def expectedLoop (parts : Parts) (values : List Value) (visit : ExpectedVisit values)
    (leading bodies : Nat) : Except Ssz.Err (Nat × Nat) :=
  match values with
  | [] => .ok (leading, bodies)
  | value :: rest =>
    let step (desc : Desc) (remaining : Parts) : Except Ssz.Err (Nat × Nat) := do
      let child ← visit value (by simp) desc
      let inline := FixedSize.isFixed desc
      expectedLoop remaining rest
        (fun value member => visit value (List.mem_cons_of_mem _ member))
        (leading + if inline then child else 4)
        (if inline then bodies else bodies + child)
    match parts with
    | .repeated element => step element (.repeated element)
    | .fields [] => .ok (leading, bodies)
    | .fields ((_, desc) :: fields) => step desc (.fields fields)
termination_by values.length

/-- Offset overflow is a final check, including for all-fixed composites. -/
def expectedTotal (total : Nat) : Except Ssz.Err Nat :=
  if 2 ^ 32 ≤ total then .error (.offsetOverflow total) else .ok total

def expectedParts (parts : Parts) (values : List Value) (visit : ExpectedVisit values) :
    Except Ssz.Err Nat := do
  let sums ← expectedLoop parts values visit 0 0
  if parts.arity values then expectedTotal (sums.1 + sums.2)
  else .error .typeMismatch

/-- Declaration order, not representation identity, determines the first match. -/
def expectedOption : List (NatOperand × Desc) → NatOperand → Except Ssz.Err Desc
  | [], selector => .error (.unknownSelector selector.value)
  | (chosen, desc) :: rest, selector =>
    if chosen.value = selector.value then .ok desc else expectedOption rest selector

def expectedBound (limit : Option NatOperand) (actual : Nat) : Except Ssz.Err Unit :=
  match limit with
  | none => .ok ()
  | some cap =>
    if actual ≤ cap.value then .ok () else .error (.overLimit cap.value actual)

def expectedStep (desc : Desc) (value : Value) (visit : ExpectedVisit value.children) :
    Except Ssz.Err Nat :=
  match desc, value with
  | .primitive shape, value => Serialize.expectedSize shape value.toPrimitive
  | .vector element length, .seq values =>
    if length.value = values.length then expectedParts (.repeated element) values visit
    else .error (.scope length.value values.length)
  | .list element limit, .seq values => do
    expectedBound (some limit) values.length
    expectedParts (.repeated element) values visit
  | .progressiveList element limit, .seq values => do
    expectedBound limit values.length
    expectedParts (.repeated element) values visit
  | .container fields, .seq values | .progressiveContainer _ fields, .seq values =>
    expectedParts (.fields fields) values visit
  | .compatibleUnion variants, .union selector value => do
    let chosen ← expectedOption variants selector
    let child ← visit value (by simp [Value.children]) chosen
    return child + 1
  | _, _ => .error .typeMismatch

/-- Pure executable measurement on arbitrary declarations and values. No encoded
byte array is constructed, and no validation or canonical-operand premise occurs. -/
def expectedSize (desc : Desc) (value : Value) : Except Ssz.Err Nat :=
  expectedStep desc value (fun child _ desc => expectedSize desc child)
termination_by value.nesting
decreasing_by exact Value.child_nesting_lt _ _ (by assumption)

private def pinnedSlots (parts : Parts) (values : List Value) :
    Except Ssz.Err (List (Bool × Ssz.Bytes)) :=
  match parts, values with
  | .repeated _, [] | .fields [], [] => .ok []
  | .repeated element, value :: rest => do
    let bytes ← Ssz.serialize element.erase value.erase
    let tail ← pinnedSlots (.repeated element) rest
    return (element.erase.isFixed, bytes) :: tail
  | .fields ((_, desc) :: fields), value :: rest => do
    let bytes ← Ssz.serialize desc.erase value.erase
    let tail ← pinnedSlots (.fields fields) rest
    return (desc.erase.isFixed, bytes) :: tail
  | _, _ => .error .typeMismatch
termination_by values.length

private def checkArity (parts : Parts) (values : List Value) (sums : Nat × Nat) :
    Except Ssz.Err (Nat × Nat) :=
  if parts.arity values then .ok sums else .error .typeMismatch

private theorem expectedLoop_pinned (parts : Parts) (values : List Value)
    (visit : ExpectedVisit values)
    (correct : ∀ value member desc,
      visit value member desc = (Ssz.serialize desc.erase value.erase).map Array.size)
    (leading bodies : Nat) :
    (expectedLoop parts values visit leading bodies).bind (checkArity parts values) =
      (pinnedSlots parts values).map
        (fun slots => (leading + Ssz.headWidth slots, bodies + Ssz.bodyWidth slots)) := by
  induction values generalizing parts leading bodies with
  | nil =>
    cases parts with
    | repeated element =>
      simp [expectedLoop, pinnedSlots, checkArity, Parts.arity,
        Except.bind, Except.map, Ssz.headWidth, Ssz.bodyWidth]
    | fields fields =>
      cases fields <;> simp [expectedLoop, pinnedSlots, checkArity, Parts.arity,
        Except.bind, Except.map, Ssz.headWidth, Ssz.bodyWidth]
  | cons value rest ih =>
    have child (desc : Desc) := correct value (by simp) desc
    have tail (remaining : Parts) (front back : Nat) :=
      ih (parts := remaining)
        (visit := fun value member => visit value (List.mem_cons_of_mem _ member))
        (correct := fun value member desc =>
          correct value (List.mem_cons_of_mem _ member) desc)
        (leading := front) (bodies := back)
    cases parts with
    | repeated element =>
      simp only [expectedLoop, pinnedSlots, child, FixedSize.isFixed_isFixed]
      cases encoded : Ssz.serialize element.erase value.erase with
      | error reason => rfl
      | ok bytes =>
        simp only [Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure]
        have next := tail (.repeated element)
          (leading + if element.erase.isFixed then bytes.size else 4)
          (if element.erase.isFixed then bodies else bodies + bytes.size)
        simp only [Except.bind, checkArity, Parts.arity, ↓reduceIte] at next ⊢
        rw [next]
        cases suffix : pinnedSlots (.repeated element) rest <;>
          cases fixed : element.erase.isFixed <;>
          simp [Except.map, Ssz.headWidth, Ssz.bodyWidth,
            Ssz.bytesPerOffset, Nat.add_assoc]
    | fields fields =>
      cases fields with
      | nil =>
        simp [expectedLoop, pinnedSlots, checkArity, Parts.arity, Except.bind, Except.map]
      | cons field fields =>
        rcases field with ⟨name, desc⟩
        simp only [expectedLoop, pinnedSlots, child, FixedSize.isFixed_isFixed]
        cases encoded : Ssz.serialize desc.erase value.erase with
        | error reason => rfl
        | ok bytes =>
          simp only [Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure]
          have next := tail (.fields fields)
            (leading + if desc.erase.isFixed then bytes.size else 4)
            (if desc.erase.isFixed then bodies else bodies + bytes.size)
          have arity : (Parts.fields ((name, desc) :: fields)).arity (value :: rest) =
              (Parts.fields fields).arity rest := by simp [Parts.arity]
          simp only [Except.bind, checkArity, arity] at next ⊢
          rw [next]
          cases suffix : pinnedSlots (.fields fields) rest <;>
            cases fixed : desc.erase.isFixed <;>
            simp [Except.map, Ssz.headWidth, Ssz.bodyWidth,
              Ssz.bytesPerOffset, Nat.add_assoc]

private theorem expectedParts_slots (parts : Parts) (values : List Value)
    (visit : ExpectedVisit values)
    (correct : ∀ value member desc,
      visit value member desc = (Ssz.serialize desc.erase value.erase).map Array.size) :
    expectedParts parts values visit = (pinnedSlots parts values).bind
      (fun slots => expectedTotal (Ssz.headWidth slots + Ssz.bodyWidth slots)) := by
  have loop := expectedLoop_pinned parts values visit correct 0 0
  have reassociate : expectedParts parts values visit =
      ((expectedLoop parts values visit 0 0).bind (checkArity parts values)).bind
        (fun sums => expectedTotal (sums.1 + sums.2)) := by
    unfold expectedParts
    cases expectedLoop parts values visit 0 0 with
    | error reason => rfl
    | ok sums =>
      simp only [Bind.bind, Except.bind, checkArity]
      split <;> rfl
  rw [reassociate, loop]
  cases pinnedSlots parts values <;> simp [Except.bind, Except.map]

private theorem map_bind {α β γ : Type} (first : Except Ssz.Err α)
    (next : α → Except Ssz.Err β) (f : β → γ) :
    (first.bind next).map f = first.bind (fun x => (next x).map f) := by
  cases first <;> rfl

private theorem pinnedSlots_repeated (element : Desc) (values : List Value) :
    pinnedSlots (.repeated element) values =
      (Ssz.serializeEach element.erase (Value.eraseList values)).map
        (fun parts => parts.map (fun bytes => (element.erase.isFixed, bytes))) := by
  induction values with
  | nil => simp [pinnedSlots, Value.eraseList, Ssz.serializeEach, Except.map]
  | cons value rest ih =>
    simp only [pinnedSlots, Value.eraseList, Ssz.serializeEach, ih]
    cases Ssz.serialize element.erase value.erase <;>
      cases Ssz.serializeEach element.erase (Value.eraseList rest) <;> rfl

private theorem pinnedSlots_fields (fields : List (String × Desc)) (values : List Value) :
    pinnedSlots (.fields fields) values =
      (Ssz.serializeFields (Desc.eraseFields fields) (Value.eraseList values)).map
        (fun parts => ((Desc.eraseFields fields).map Ssz.Desc.isFixed).zip parts) := by
  induction values generalizing fields with
  | nil =>
    cases fields <;>
      simp [pinnedSlots, Desc.eraseFields, Value.eraseList, Ssz.serializeFields, Except.map]
  | cons value rest ih =>
    cases fields with
    | nil =>
      simp [pinnedSlots, Desc.eraseFields, Value.eraseList, Ssz.serializeFields, Except.map]
    | cons field fields =>
      rcases field with ⟨name, desc⟩
      simp only [pinnedSlots, Value.eraseList, Desc.eraseFields, Ssz.serializeFields, ih]
      cases Ssz.serialize desc.erase value.erase <;>
        cases Ssz.serializeFields (Desc.eraseFields fields) (Value.eraseList rest) <;> rfl

private theorem assemble_size_map (inline : List Bool) (parts : List Ssz.Bytes) :
    (Ssz.assemble inline parts).map Array.size =
      expectedTotal (Ssz.headWidth (inline.zip parts) + Ssz.bodyWidth (inline.zip parts)) := by
  unfold Ssz.assemble expectedTotal
  simp only [Ssz.bytesPerOffset]
  split <;>
    simp [Except.map, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
      Pure.pure, Except.pure, Ssz.headOf_size, Ssz.bodiesOf_size]

private theorem zip_constant (fixed : Bool) (parts : List Ssz.Bytes) :
    (parts.map (fun _ => fixed)).zip parts = parts.map (fun bytes => (fixed, bytes)) := by
  induction parts with
  | nil => rfl
  | cons bytes rest ih => simp only [List.map_cons, List.zip_cons_cons, ih]

/-- Sequence refinement preserves all child errors, including errors preceding
an overflowing accumulated size. -/
theorem expectedParts_repeated_eq (element : Desc) (values : List Value)
    (visit : ExpectedVisit values)
    (correct : ∀ value member desc,
      visit value member desc = (Ssz.serialize desc.erase value.erase).map Array.size) :
    expectedParts (.repeated element) values visit =
      (Ssz.serializeSequence element.erase (Value.eraseList values)).map Array.size := by
  rw [expectedParts_slots _ _ _ correct, pinnedSlots_repeated]
  simp only [Ssz.serializeSequence, Bind.bind, map_bind]
  cases Ssz.serializeEach element.erase (Value.eraseList values) with
  | error reason => rfl
  | ok parts =>
    change expectedTotal _ = (Ssz.assemble _ parts).map Array.size
    rw [assemble_size_map, zip_constant]

/-- Field refinement includes mismatched arity after a successful paired prefix. -/
theorem expectedParts_fields_eq (fields : List (String × Desc)) (values : List Value)
    (visit : ExpectedVisit values)
    (correct : ∀ value member desc,
      visit value member desc = (Ssz.serialize desc.erase value.erase).map Array.size) :
    expectedParts (.fields fields) values visit =
      (Ssz.serializeStruct (Desc.eraseFields fields) (Value.eraseList values)).map Array.size := by
  rw [expectedParts_slots _ _ _ correct, pinnedSlots_fields]
  simp only [Ssz.serializeStruct, Bind.bind, map_bind]
  cases Ssz.serializeFields (Desc.eraseFields fields) (Value.eraseList values) with
  | error reason => rfl
  | ok parts =>
    change expectedTotal _ = (Ssz.assemble _ parts).map Array.size
    exact (assemble_size_map _ parts).symm

theorem expectedOption_eq (variants : List (NatOperand × Desc)) (selector : NatOperand) :
    (expectedOption variants selector).map Desc.erase =
      Ssz.lookupOption (variants.map (fun variant => variant.1.value))
        (Desc.eraseVariants variants) selector.value := by
  induction variants with
  | nil => rfl
  | cons variant rest ih =>
    rcases variant with ⟨chosen, desc⟩
    simp only [expectedOption, List.map_cons, Desc.eraseVariants, Ssz.lookupOption]
    by_cases same : chosen.value = selector.value
    · simp [same, Except.map]
    · simpa only [same, beq_iff_eq, ↓reduceIte] using ih

theorem expectedBound_eq (limit : Option NatOperand) (actual : Nat) :
    expectedBound limit actual = Ssz.boundCheck (limit.map NatOperand.value) actual := by
  cases limit <;> rfl

/-- A single constructor layer agrees with the pinned serializer whenever its
actual-child callback does. Wrong value kinds need no callback assumptions. -/
theorem expectedStep_eq_pinned (desc : Desc) (value : Value)
    (visit : ExpectedVisit value.children)
    (correct : ∀ child member desc,
      visit child member desc = (Ssz.serialize desc.erase child.erase).map Array.size) :
    expectedStep desc value visit = (Ssz.serialize desc.erase value.erase).map Array.size := by
  cases desc with
  | primitive shape =>
    simpa only [expectedStep, Desc.erase_primitive, Value.erase_toPrimitive] using
      Serialize.expectedSize_eq_pinned shape value.toPrimitive
  | vector element length =>
    cases value <;> simp only [expectedStep, Desc.erase_vector, Value.erase,
      Ssz.serialize, Except.map]
    rename_i values
    by_cases same : length.value = values.length
    · simp only [Value.eraseList_length, same, beq_self_eq_true, ↓reduceIte]
      exact expectedParts_repeated_eq element values visit correct
    · have reverse : values.length ≠ length.value := Ne.symm same
      simp [same, reverse]
  | list element limit =>
    cases value <;> simp only [expectedStep, Desc.erase_list, Value.erase,
      Ssz.serialize, Except.map]
    rename_i values
    simp only [expectedBound, Value.eraseList_length]
    by_cases fits : values.length ≤ limit.value <;>
      simp only [fits, ↓reduceIte, Bind.bind, Except.bind]
    exact expectedParts_repeated_eq element values visit correct
  | progressiveList element limit =>
    cases value <;> simp only [expectedStep, Desc.erase_progressiveList, Value.erase,
      Ssz.serialize, Except.map]
    rename_i values
    rw [expectedBound_eq, Value.eraseList_length]
    cases Ssz.boundCheck (limit.map NatOperand.value) values.length with
    | error reason => rfl
    | ok passed => exact expectedParts_repeated_eq element values visit correct
  | container fields =>
    cases value <;> simp only [expectedStep, Desc.erase_container, Value.erase,
      Ssz.serialize, Except.map]
    exact expectedParts_fields_eq fields _ visit correct
  | progressiveContainer active fields =>
    cases value <;> simp only [expectedStep, Desc.erase_progressiveContainer, Value.erase,
      Ssz.serialize, Except.map]
    exact expectedParts_fields_eq fields _ visit correct
  | compatibleUnion variants =>
    cases value <;> simp only [expectedStep, Desc.erase_compatibleUnion, Value.erase,
      Ssz.serialize, Except.map]
    rename_i selector child
    rw [← expectedOption_eq]
    cases selected : expectedOption variants selector with
    | error reason => rfl
    | ok chosen =>
      simp only [Except.map, Bind.bind, Except.bind]
      rw [correct child (by simp [Value.children]) chosen]
      cases Ssz.serialize chosen.erase child.erase <;>
        simp [Except.map, Pure.pure, Except.pure, Nat.add_comm]

/-- Exact size and exact semantic failure for every constructor and every value
kind. Raw widths, selectors, active masks and noncanonical operands are unrestricted. -/
theorem expectedSize_eq_pinned (desc : Desc) (value : Value) :
    expectedSize desc value = (Ssz.serialize desc.erase value.erase).map Array.size := by
  rw [expectedSize]
  apply expectedStep_eq_pinned
  intro child member chosen
  exact expectedSize_eq_pinned chosen child
termination_by value.nesting
decreasing_by exact Value.child_nesting_lt _ _ member

end SszNative.CodecMeasure

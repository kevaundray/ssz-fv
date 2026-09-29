import SszCodecEmitSemanticBase

set_option autoImplicit false

namespace SszNative.CodecEmit

open Codec (Desc Value)
open CodecMeasure (Plan Parts)

/-- Width comparison for the actual paired children. The callback is restricted
to actual values, making the subsequent recursive proof structurally decreasing. -/
theorem generatedChildren_sizes_of (parts : Parts) (values : List Value) (keep : Bool)
    (plans : List Plan) (front back : Nat) (slots : List (Bool × Ssz.Bytes))
    (generated : GeneratedChildren parts values keep plans front back)
    (semantic : ByteChildren parts values slots)
    (correct : ∀ value, value ∈ values → ∀ desc retain plan bytes,
      Generated desc value retain plan → Ssz.serialize desc.erase value.erase = .ok bytes →
      plan.size.value = bytes.size) :
    front = Ssz.headWidth slots ∧ back = Ssz.bodyWidth slots := by
  cases semantic with
  | repeatedNil desc =>
    cases generated
    exact ⟨rfl, rfl⟩
  | fieldsNil =>
    cases generated
    exact ⟨rfl, rfl⟩
  | repeated desc value values bytes slots encoded remaining =>
    cases generated with
    | repeated _ _ _ _ child plans front back childGenerated restGenerated =>
      have size := correct value (by simp) desc keep child bytes childGenerated encoded
      have rest := generatedChildren_sizes_of (.repeated desc) values keep plans front back slots
        restGenerated remaining (fun value member => correct value (List.mem_cons_of_mem _ member))
      cases FixedSize.isFixed desc <;>
        simp only [Bool.false_eq_true, ↓reduceIte, Ssz.headWidth, Ssz.bodyWidth,
          Ssz.bytesPerOffset, size, rest.1, rest.2, Nat.zero_add]
      <;> exact ⟨True.intro, True.intro⟩
  | fields name desc fields value values bytes slots encoded remaining =>
    cases generated with
    | fields _ _ _ _ _ _ child plans front back childGenerated restGenerated =>
      have size := correct value (by simp) desc keep child bytes childGenerated encoded
      have rest := generatedChildren_sizes_of (.fields fields) values keep plans front back slots
        restGenerated remaining (fun value member => correct value (List.mem_cons_of_mem _ member))
      cases FixedSize.isFixed desc <;>
        simp only [Bool.false_eq_true, ↓reduceIte, Ssz.headWidth, Ssz.bodyWidth,
          Ssz.bytesPerOffset, size, rest.1, rest.2, Nat.zero_add]
      <;> exact ⟨True.intro, True.intro⟩
termination_by values.length

/-- A generated plan's mathematical size agrees with the successful pinned
encoding, even for a non-retained witness whose child arrays were discarded. -/
theorem generated_size (desc : Desc) (value : Value) (retain : Bool) (plan : Plan)
    (bytes : Ssz.Bytes) (generated : Generated desc value retain plan)
    (semantic : Ssz.serialize desc.erase value.erase = .ok bytes) :
    plan.size.value = bytes.size := by
  have childSize (child : Value) (member : child ∈ value.children) (childDesc : Desc)
      (childRetain : Bool) (childPlan : Plan) (childBytes : Ssz.Bytes)
      (childGenerated : Generated childDesc child childRetain childPlan)
      (childSemantic : Ssz.serialize childDesc.erase child.erase = .ok childBytes) :
      childPlan.size.value = childBytes.size :=
    generated_size childDesc child childRetain childPlan childBytes childGenerated childSemantic
  cases generated with
  | primitive shape value retain size expected =>
    change Ssz.serialize shape.erase value.erase = .ok bytes at semantic
    change size.value = bytes.size
    have comparison := Serialize.expectedSize_eq_pinned shape value.toPrimitive
    rw [expected, Value.erase_toPrimitive, semantic] at comparison
    exact Except.ok.inj comparison
  | parts desc parts values retain plan plans front back shape arity generated size leading children =>
    obtain ⟨slots, encoded, assembled⟩ := composite_byteChildren desc parts values shape bytes semantic
    have widths := generatedChildren_sizes_of parts values _ plans front back slots generated encoded
      (fun child member childDesc childRetain childPlan childBytes childGenerated childSemantic =>
        childSize child (by simpa only [Value.children] using member)
          childDesc childRetain childPlan childBytes childGenerated childSemantic)
    rw [size, widths.1, widths.2, assembled, Array.size_append, Ssz.headOf_size, Ssz.bodiesOf_size]
  | union variants selector value retain chosen child plan option generated size children =>
    have selected := refines_success id _ _ chosen
      (CodecMeasure.option_refines variants selector 0) option
    have lookup := CodecMeasure.expectedOption_eq variants selector
    rw [selected] at lookup
    have choice : Ssz.lookupOption (variants.map (fun variant => variant.1.value))
        (Desc.eraseVariants variants) selector.value = .ok chosen.erase := by
      simpa only [Except.map, id_eq] using lookup.symm
    simp only [Desc.erase_compatibleUnion, Value.erase, Ssz.serialize, choice,
      Bind.bind, Except.bind] at semantic
    cases encoded : Ssz.serialize chosen.erase value.erase with
    | error reason => simp only [encoded] at semantic; cases semantic
    | ok body =>
      simp only [encoded, Pure.pure, Except.pure, Except.ok.injEq] at semantic
      have width := childSize value (by simp [Value.children]) chosen retain child body generated encoded
      rw [← semantic, Array.size_append, Array.size_singleton, size, width]
      omega
termination_by value.nesting
decreasing_by exact Value.child_nesting_lt _ _ member

/-- Combined table-width endpoint for consumers of generated-plan evidence. -/
theorem generatedChildren_sizes (parts : Parts) (values : List Value) (keep : Bool)
    (plans : List Plan) (front back : Nat) (slots : List (Bool × Ssz.Bytes))
    (generated : GeneratedChildren parts values keep plans front back)
    (semantic : ByteChildren parts values slots) :
    front = Ssz.headWidth slots ∧ back = Ssz.bodyWidth slots := by
  exact generatedChildren_sizes_of parts values keep plans front back slots generated semantic
    (fun value _ desc retain plan bytes generated semantic =>
      generated_size desc value retain plan bytes generated semantic)

end SszNative.CodecEmit

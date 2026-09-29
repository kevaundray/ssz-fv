import SszCodecEmitPlans
import SszCodecEmitMemory
import SszCodecEmitSafety
import SszCodecEmitSemanticBase
import SszCodecEmitSizes

set_option autoImplicit false

namespace SszNative.CodecEmit

open Codec (Desc Value)
open CodecMeasure (Plan Parts)


/-- Primitive byte correctness reuses the limb and dirty-padding mask bridge;
no canonicality or logical operand-width assumption is introduced. -/
theorem primitive_emit_encodes (shape : Serialize.Desc) (value : Value)
    (size : Nat) (out : Slice)
    (expected : Serialize.expectedSize shape value.toPrimitive = .ok size)
    (fits : size ≤ out.length) (host : out.length < 2 ^ 64) :
    Encodes (primitive shape value out).writes out.address
      (Serialize.emit shape value.toPrimitive) := by
  have emittedSize := (Serialize.expected_encoding shape value.toPrimitive).2 size expected
  have copied := copy_encodes out (Serialize.emit shape value.toPrimitive) (by omega)
  have success := primitive_emit_success shape value size out expected fits host
  cases shape <;> cases value <;>
    simp only [primitive] at success ⊢ <;>
    try { exact copied } <;>
    try { cases success }
  rename_i width number
  cases converted : (CodecMeasure.hostSize width 0).result with
  | error reason => simp [converted, returned, bind, Except.mapError] at success
  | ok actual =>
    simpa only [converted, returned, bind, Except.mapError, List.nil_append] using copied

/-- Local induction contract. Its execution facts are derived from the
structural safety theorem, never required of a public caller. -/
def SemanticVisit (values : List Value) (visit : Visit values) : Prop :=
  ∀ value member desc retain plan supplied out bytes,
    Generated desc value retain plan →
    (retain = true ∨ FixedSize.isFixed desc = true) →
    children supplied = plan.children →
    (plan.children ≠ [] → leading supplied = plan.leading) →
    plan.size.value ≤ out.length → out.length < 2 ^ 64 →
    Ssz.serialize desc.erase value.erase = .ok bytes →
    (visit value member desc supplied out).result = .ok plan.size.value ∧
      Encodes (visit value member desc supplied out).writes out.address bytes

theorem SemanticVisit.tail (value : Value) (values : List Value)
    (visit : Visit (value :: values)) (correct : SemanticVisit _ visit) :
    SemanticVisit values
      (fun child member => visit child (List.mem_cons_of_mem value member)) := by
  intro child member
  exact correct child (List.mem_cons_of_mem value member)

private theorem hostSize_ok (size : NatOperand) (bound : size.value < 2 ^ 64) :
    (CodecMeasure.hostSize size 0).result = .ok size.value := by
  exact hostSize_success size 0 bound

private theorem sequential_byteChildren (parts : Parts) (values : List Value)
    (slots : List (Bool × Ssz.Bytes)) (encoded : ByteChildren parts values slots)
    (keep : Bool) (plans : List Plan) (front back : Nat)
    (generated : GeneratedChildren parts values keep plans front back)
    (fixed : parts.allFixed = true) (visit : Visit values)
    (correct : SemanticVisit values visit) (out : Slice) (position start : Nat)
    (fits : position + front + back ≤ out.length) (host : out.length < 2 ^ 64) :
    Encodes (sequential parts values visit out position).writes (out.address + position)
      (Ssz.headOf start slots ++ Ssz.bodiesOf slots) := by
  induction encoded generalizing plans front back position with
  | repeatedNil desc =>
    simpa only [sequential, pure, Ssz.headOf, Ssz.bodiesOf, Array.empty_append] using
      Encodes.empty (out.address + position)
  | fieldsNil =>
    simpa only [sequential, pure, Ssz.headOf, Ssz.bodiesOf, Array.empty_append] using
      Encodes.empty (out.address + position)
  | repeated desc value values bytes slots semantic remaining ih =>
    cases generated with
    | repeated _ _ _ _ child plans front back childGenerated tailGenerated =>
      have childFixed : FixedSize.isFixed desc = true := fixed
      have width := generated_size desc value keep child bytes childGenerated semantic
      have noChildren := generated_fixed_children desc value keep child childGenerated childFixed
      have total : position + child.size.value + front + back ≤ out.length := by
        simpa only [childFixed, ↓reduceIte, Nat.zero_add, Nat.add_assoc] using fits
      have run := correct value (by simp) desc keep child none
        ⟨out.address + position, out.length - position⟩ bytes childGenerated
        (Or.inr childFixed) (by simpa only [children] using noChildren.symm)
        (by simp only [noChildren, ne_eq, not_true_eq_false, false_implies])
        (by dsimp; omega) (by dsimp; omega) semantic
      have rest := ih plans front back tailGenerated fixed
        (fun child member => visit child (List.mem_cons_of_mem _ member))
        (correct.tail value values visit) (position + child.size.value) (by omega)
      have joined := run.2.append (by
        simpa only [width, Nat.add_assoc] using rest)
      simp only [sequential, nextPart, pure, bind, suffix,
        show position ≤ out.length by omega, ↓reduceIte, run.1,
        List.nil_append, childFixed, Ssz.headOf, Ssz.bodiesOf,
        Array.append_assoc]
      simpa only [width] using joined
  | fields name desc fields value values bytes slots semantic remaining ih =>
    cases generated with
    | fields _ _ _ _ _ _ child plans front back childGenerated tailGenerated =>
      have fixedBoth : FixedSize.isFixed desc = true ∧
          (Parts.fields fields).allFixed = true := by
        simpa only [Parts.allFixed, FixedSize.fieldsFixed, Bool.and_eq_true] using fixed
      have width := generated_size desc value keep child bytes childGenerated semantic
      have noChildren := generated_fixed_children desc value keep child childGenerated fixedBoth.1
      have total : position + child.size.value + front + back ≤ out.length := by
        simpa only [fixedBoth.1, ↓reduceIte, Nat.zero_add, Nat.add_assoc] using fits
      have run := correct value (by simp) desc keep child none
        ⟨out.address + position, out.length - position⟩ bytes childGenerated
        (Or.inr fixedBoth.1) (by simpa only [children] using noChildren.symm)
        (by simp only [noChildren, ne_eq, not_true_eq_false, false_implies])
        (by dsimp; omega) (by dsimp; omega) semantic
      have rest := ih plans front back tailGenerated fixedBoth.2
        (fun child member => visit child (List.mem_cons_of_mem _ member))
        (correct.tail value values visit) (position + child.size.value) (by omega)
      have joined := run.2.append (by
        simpa only [width, Nat.add_assoc] using rest)
      simp only [sequential, nextPart, pure, bind, suffix,
        show position ≤ out.length by omega, ↓reduceIte, run.1,
        List.nil_append, fixedBoth.1, Ssz.headOf, Ssz.bodiesOf,
        Array.append_assoc]
      simpa only [width] using joined

private theorem table_byteChildren (parts : Parts) (values : List Value)
    (slots : List (Bool × Ssz.Bytes)) (encoded : ByteChildren parts values slots)
    (plans : List Plan) (front back : Nat)
    (generated : GeneratedChildren parts values true plans front back)
    (mode : ∀ element, parts = .repeated element → FixedSize.isFixed element = false)
    (visit : Visit values) (correct : SemanticVisit values visit)
    (out : Slice) (head body : Nat)
    (separated : head + front ≤ body) (fits : body + back ≤ out.length)
    (host : out.length < 2 ^ 64) :
    EncodesParts (table parts values visit plans out head body).writes
      (out.address + head) (out.address + body)
      (Ssz.headOf body slots) (Ssz.bodiesOf slots) := by
  induction encoded generalizing plans front back head body with
  | repeatedNil desc =>
    simpa only [table, pure, Ssz.headOf, Ssz.bodiesOf] using
      EncodesParts.empty (out.address + head) (out.address + body)
  | fieldsNil =>
    simpa only [table, pure, Ssz.headOf, Ssz.bodiesOf] using
      EncodesParts.empty (out.address + head) (out.address + body)
  | repeated desc value values bytes slots semantic remaining ih =>
    cases generated with
    | repeated _ _ _ _ child plans front back childGenerated tailGenerated =>
      have notFixed := mode desc rfl
      have width := generated_size desc value true child bytes childGenerated semantic
      have sums := generatedChildren_sizes _ _ _ _ _ _ _ tailGenerated remaining
      have sep : head + 4 + front ≤ body := by
        simpa only [notFixed, Bool.false_eq_true, ↓reduceIte, Nat.add_assoc] using separated
      have room : body + child.size.value + back ≤ out.length := by
        simpa only [notFixed, Bool.false_eq_true, ↓reduceIte, Nat.add_assoc] using fits
      have run := correct value (by simp) desc true child (some child)
        ⟨out.address + body, child.size.value⟩ bytes childGenerated (Or.inl rfl)
        rfl (fun _ => rfl) (Nat.le_refl _) (by dsimp; omega) semantic
      have rest := ih plans front back tailGenerated mode
        (fun child member => visit child (List.mem_cons_of_mem _ member))
        (correct.tail value values visit) (head + 4) (body + child.size.value)
        (by omega) (by omega)
      have offset := Encodes.singleton (out.address + head) (Ssz.uintBytes 4 body)
      have joined := EncodesParts.variable offset run.2 (by
        simpa only [Ssz.uintBytes_size, width, Nat.add_assoc] using rest)
        (by dsimp only; rw [Ssz.headOf_size, ← sums.1, Ssz.uintBytes_size]; omega)
      simp only [table, nextPart, pure, bind, returned,
        hostSize_ok child.size (by omega), Except.mapError, inline,
        Bool.false_eq_true, ↓reduceIte, sub,
        show head + 4 ≤ out.length by omega,
        show body + child.size.value ≤ out.length by omega,
        copy, Ssz.uintBytes_size, Nat.le_refl, run.1, List.nil_append,
        notFixed, Ssz.headOf, Ssz.bodiesOf]
      simpa only [width, List.append_assoc, Ssz.bytesPerOffset] using joined
  | fields name desc fields value values bytes slots semantic remaining ih =>
    cases generated with
    | fields _ _ _ _ _ _ child plans front back childGenerated tailGenerated =>
      have width := generated_size desc value true child bytes childGenerated semantic
      have sums := generatedChildren_sizes _ _ _ _ _ _ _ tailGenerated remaining
      have remainingMode : ∀ element, Parts.fields fields = .repeated element →
          FixedSize.isFixed element = false := by intro element impossible; cases impossible
      cases fixed : FixedSize.isFixed desc with
      | true =>
        have sep : head + child.size.value + front ≤ body := by
          simpa only [fixed, ↓reduceIte, Nat.add_assoc] using separated
        have room : body + back ≤ out.length := by
          simpa only [fixed, ↓reduceIte, Nat.zero_add] using fits
        have run := correct value (by simp) desc true child (some child)
          ⟨out.address + head, child.size.value⟩ bytes childGenerated (Or.inl rfl)
          rfl (fun _ => rfl) (Nat.le_refl _) (by dsimp; omega) semantic
        have rest := ih plans front back tailGenerated remainingMode
          (fun child member => visit child (List.mem_cons_of_mem _ member))
          (correct.tail value values visit) (head + child.size.value) body
          (by omega) room
        have joined := EncodesParts.inline run.2 (by
          simpa only [width, Nat.add_assoc] using rest)
        simp only [table, nextPart, pure, bind, returned,
          hostSize_ok child.size (by omega), Except.mapError, inline, fixed,
          ↓reduceIte, sub, show head + child.size.value ≤ out.length by omega,
          run.1, List.nil_append, Ssz.headOf, Ssz.bodiesOf]
        simpa only [width] using joined
      | false =>
        have sep : head + 4 + front ≤ body := by
          simpa only [fixed, Bool.false_eq_true, ↓reduceIte, Nat.add_assoc] using separated
        have room : body + child.size.value + back ≤ out.length := by
          simpa only [fixed, Bool.false_eq_true, ↓reduceIte, Nat.add_assoc] using fits
        have run := correct value (by simp) desc true child (some child)
          ⟨out.address + body, child.size.value⟩ bytes childGenerated (Or.inl rfl)
          rfl (fun _ => rfl) (Nat.le_refl _) (by dsimp; omega) semantic
        have rest := ih plans front back tailGenerated remainingMode
          (fun child member => visit child (List.mem_cons_of_mem _ member))
          (correct.tail value values visit) (head + 4) (body + child.size.value)
          (by omega) (by omega)
        have offset := Encodes.singleton (out.address + head) (Ssz.uintBytes 4 body)
        have joined := EncodesParts.variable offset run.2 (by
          simpa only [Ssz.uintBytes_size, width, Nat.add_assoc] using rest)
          (by dsimp only; rw [Ssz.headOf_size, ← sums.1, Ssz.uintBytes_size]; omega)
        simp only [table, nextPart, pure, bind, returned,
          hostSize_ok child.size (by omega), Except.mapError, inline, fixed,
          Bool.false_eq_true, ↓reduceIte, sub,
          show head + 4 ≤ out.length by omega,
          show body + child.size.value ≤ out.length by omega,
          copy, Ssz.uintBytes_size, Nat.le_refl, run.1, List.nil_append,
          Ssz.headOf, Ssz.bodiesOf]
        simpa only [width, List.append_assoc, Ssz.bytesPerOffset] using joined

private theorem emitParts_byteChildren (parts : Parts) (values : List Value)
    (visit : Visit values) (correct : SemanticVisit values visit) (retain : Bool)
    (plan : Plan) (plans : List Plan) (front back : Nat)
    (generated : GeneratedChildren parts values (retain && !parts.allFixed) plans front back)
    (arity : parts.arity values = true) (usable : retain = true ∨ parts.allFixed = true)
    (size : plan.size.value = front + back) (frontSize : plan.leading = front)
    (retained : plan.children = if retain && !parts.allFixed then plans else [])
    (supplied : Option Plan) (sameChildren : children supplied = plan.children)
    (sameLeading : plan.children ≠ [] → leading supplied = plan.leading)
    (out : Slice) (fits : plan.size.value ≤ out.length) (host : out.length < 2 ^ 64)
    (slots : List (Bool × Ssz.Bytes)) (encoded : ByteChildren parts values slots) :
    Encodes (emitParts parts values visit supplied out).writes out.address
      (Ssz.headOf (Ssz.headWidth slots) slots ++ Ssz.bodiesOf slots) := by
  by_cases fixed : parts.allFixed = true
  · have keep : (retain && !parts.allFixed) = false := by
      simp only [fixed, Bool.not_true, Bool.and_false]
    rw [keep] at generated retained
    have noChildren : children supplied = [] := by
      simpa only [Bool.false_eq_true, ↓reduceIte] using sameChildren.trans retained
    rw [emitParts, noChildren]
    simp only [List.isEmpty_nil, ↓reduceIte]
    simpa only [Nat.add_zero] using
      sequential_byteChildren parts values slots encoded false plans front back generated
        fixed visit correct out 0 (Ssz.headWidth slots) (by omega) host
  · have notFixed : parts.allFixed = false := by
      cases equal : parts.allFixed <;> simp_all
    have retainedTrue : retain = true := usable.resolve_right fixed
    have keep : (retain && !parts.allFixed) = true := by
      simp only [retainedTrue, notFixed, Bool.not_false, Bool.and_true]
    rw [keep] at generated retained
    have actual : children supplied = plans := by
      simpa only [↓reduceIte] using sameChildren.trans retained
    cases plans with
    | nil =>
      have empty := generatedChildren_empty parts values true [] front back generated arity rfl
      subst values
      cases encoded <;>
        simpa only [emitParts, actual, List.isEmpty_nil, ↓reduceIte, sequential,
          pure, Ssz.headOf, Ssz.bodiesOf, Array.empty_append] using Encodes.empty out.address
    | cons child plans =>
      have nonempty : plan.children ≠ [] := by rw [retained]; simp
      have leadingSize : leading supplied = front := (sameLeading nonempty).trans frontSize
      have sums := generatedChildren_sizes parts values true (child :: plans) front back slots
        generated encoded
      have run := table_byteChildren parts values slots encoded (child :: plans) front back
        generated (by intro element equal; subst parts; exact notFixed) visit correct out 0 front
        (by omega) (by omega) host
      have joined := run.contiguous (by rw [Ssz.headOf_size, ← sums.1]; omega)
      simpa only [emitParts, actual, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        leadingSize, Nat.add_zero, sums.1] using joined

/-- Ordered native writes implement the pinned bytes from a past-generated
plan. The supplied optional plan need only agree on retained children and the
leading width when those children exist. Bounds and successful execution are
proved internally, including non-retained fixed descendants. -/
theorem generated_emit_encodes (desc : Desc) (value : Value) (retain : Bool)
    (plan : Plan) (supplied : Option Plan) (out : Slice) (bytes : Ssz.Bytes)
    (generated : Generated desc value retain plan)
    (usable : retain = true ∨ FixedSize.isFixed desc = true)
    (sameChildren : children supplied = plan.children)
    (sameLeading : plan.children ≠ [] → leading supplied = plan.leading)
    (fits : plan.size.value ≤ out.length) (host : out.length < 2 ^ 64)
    (semantic : Ssz.serialize desc.erase value.erase = .ok bytes) :
    Encodes (emit desc value supplied out).writes out.address bytes := by
  rw [emit]
  have correct : SemanticVisit value.children
      (fun child _ desc supplied out => emit desc child supplied out) := by
    intro child member desc retain plan supplied out bytes generated usable
      sameChildren sameLeading fits host semantic
    exact ⟨generated_emit_success desc child retain plan supplied out generated usable
      sameChildren sameLeading fits host,
      generated_emit_encodes desc child retain plan supplied out bytes generated usable
        sameChildren sameLeading fits host semantic⟩
  cases generated with
  | primitive shape value retain size expected =>
    change Ssz.serialize shape.erase value.erase = .ok bytes at semantic
    have encoding := (Serialize.expected_encoding shape value.toPrimitive).1
    rw [expected] at encoding
    have equal : bytes = Serialize.emit shape value.toPrimitive := by
      simpa only [Value.erase_toPrimitive, semantic, Except.map, Except.ok.injEq] using encoding
    rw [equal]
    exact primitive_emit_encodes shape value size.value out expected fits host
  | parts desc parts values retain plan plans front back shape arity generated size frontSize retained =>
    obtain ⟨slots, encoded, assembled⟩ :=
      composite_byteChildren desc parts values shape bytes semantic
    rw [assembled]
    have available : retain = true ∨ parts.allFixed = true :=
      usable.imp_right (composite_fixed desc parts shape)
    have run := emitParts_byteChildren parts values _ correct retain plan plans front back generated
      arity available size frontSize retained supplied sameChildren sameLeading out fits host slots encoded
    cases shape <;> exact run
  | union variants selector value retain chosen child plan option generated size retained =>
    have retainedTrue : retain = true := by
      rcases usable with retained | fixed
      · exact retained
      · simp only [FixedSize.isFixed, Bool.false_eq_true] at fixed
    have childChildren : children ((children supplied).head?) = child.children := by
      rw [sameChildren, retained, retainedTrue]
      cases empty : child.children <;> simp only [empty, List.isEmpty_nil, List.isEmpty_cons,
        Bool.not_true, Bool.not_false, Bool.and_false, Bool.and_true, Bool.false_eq_true,
        ↓reduceIte, List.head?, children]
    have childLeading : child.children ≠ [] →
        leading ((children supplied).head?) = child.leading := by
      intro nonempty
      rw [sameChildren, retained, retainedTrue]
      cases empty : child.children with
      | nil => exact False.elim (nonempty empty)
      | cons first rest => simp only [List.isEmpty_cons, Bool.not_false, Bool.and_true,
          ↓reduceIte, List.head?, leading]
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
      have run := correct value (by simp [Value.children]) chosen retain child
        ((children supplied).head?) ⟨out.address + 1, out.length - 1⟩ body generated
        (Or.inl retainedTrue) childChildren childLeading (by dsimp; omega) (by dsimp; omega) encoded
      have selectorEncoded := Encodes.singleton out.address #[UInt8.ofNat selector.value]
      have joined := selectorEncoded.append (by simpa only [Array.size_singleton] using run.2)
      rw [← semantic]
      simpa only [emitStep, copy, Array.size_singleton,
        show 1 ≤ out.length by omega, ↓reduceIte, bind, returned, option,
        Except.mapError, suffix, run.1, pure, List.nil_append, List.append_nil] using joined
termination_by value.nesting
decreasing_by exact Value.child_nesting_lt _ _ (by assumption)

end SszNative.CodecEmit

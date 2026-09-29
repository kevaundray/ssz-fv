import SszX86.CodecEmitPartsInvariant

set_option autoImplicit false

namespace SszX86.CodecEmitParts
open SszNative
open SszNative.Codec (Desc Value)
open SszNative.CodecMeasure (Plan Parts)

/-- In the fixed sequential loop no runtime plan is supplied. The child keeps
the original output suffix, including any as-yet-unwritten siblings. -/
theorem sequential_repeated_child (element : Desc) (value : Value) (values : List Value)
    (child : Plan) (plans : List Plan) (front back capacity position : Nat)
    (generated : SszNative.CodecEmit.GeneratedChildren (.repeated element)
      (value :: values) false (child :: plans) front back)
    (fixed : FixedSize.isFixed element = true)
    (fits : position + front + back ≤ capacity) (host : capacity < 2 ^ 64) :
    SszX86.CodecEmit.GeneratedCall element value none (capacity - position) ∧
      ∃ remainingFront remainingBack,
        SszNative.CodecEmit.GeneratedChildren (.repeated element) values false plans
          remainingFront remainingBack ∧
        position + child.size.value + remainingFront + remainingBack ≤ capacity ∧
        front + back = child.size.value + remainingFront + remainingBack := by
  cases generated with
  | repeated element value values keep child plans remainingFront remainingBack childGenerated remaining =>
    have empty := SszNative.CodecEmit.generated_fixed_children element value false child childGenerated fixed
    simp only [fixed, ↓reduceIte, Nat.zero_add] at fits ⊢
    refine ⟨⟨false, child, childGenerated, Or.inr fixed, ?_, ?_, by omega, by omega⟩,
      remainingFront, remainingBack, remaining, by omega, by omega⟩
    · simpa only [SszNative.CodecEmit.children] using empty.symm
    · intro nonempty
      exact False.elim (nonempty empty)

theorem sequential_field_child (name : String) (desc : Desc)
    (fields : List (String × Desc)) (value : Value) (values : List Value)
    (child : Plan) (plans : List Plan) (front back capacity position : Nat)
    (generated : SszNative.CodecEmit.GeneratedChildren (.fields ((name, desc) :: fields))
      (value :: values) false (child :: plans) front back)
    (fixed : Parts.allFixed (.fields ((name, desc) :: fields)) = true)
    (arity : Parts.arity (.fields ((name, desc) :: fields)) (value :: values) = true)
    (fits : position + front + back ≤ capacity) (host : capacity < 2 ^ 64) :
    SszX86.CodecEmit.GeneratedCall desc value none (capacity - position) ∧
      SequentialInvariant (.fields fields) values capacity (position + child.size.value) := by
  have both : FixedSize.isFixed desc = true ∧ Parts.allFixed (.fields fields) = true := by
    simpa only [Parts.allFixed, FixedSize.fieldsFixed, Bool.and_eq_true] using fixed
  have tailArity : Parts.arity (.fields fields) values = true := by
    simpa [Parts.arity] using arity
  cases generated with
  | fields name desc fields value values keep child plans remainingFront remainingBack childGenerated remaining =>
    have empty := SszNative.CodecEmit.generated_fixed_children desc value false child childGenerated both.1
    simp only [both.1, ↓reduceIte, Nat.zero_add] at fits
    refine ⟨⟨false, child, childGenerated, Or.inr both.1, ?_, ?_, by omega, by omega⟩,
      ⟨plans, remainingFront, remainingBack, remaining, tailArity, both.2, by omega, host⟩⟩
    · simpa only [SszNative.CodecEmit.children] using empty.symm
    · intro nonempty
      exact False.elim (nonempty empty)

/-- Variable repeated children always use offset heads and retained body slices;
their child size is proved host-sized before the actual Nat narrowing loop. -/
theorem table_repeated_child (element : Desc) (value : Value) (values : List Value)
    (child : Plan) (plans : List Plan) (capacity head body : Nat)
    (h : TableInvariant (.repeated element) (value :: values) (child :: plans) capacity head body) :
    SszX86.CodecEmit.GeneratedCall element value (some child) child.size.value ∧
      head + 4 ≤ body ∧ body + child.size.value ≤ capacity ∧
      TableInvariant (.repeated element) values plans capacity (head + 4) (body + child.size.value) := by
  rcases h with ⟨front, back, generated, arity, variable, headFits, bodyFits, host⟩
  have notFixed := variable element rfl
  cases generated with
  | repeated element value values keep child plans remainingFront remainingBack childGenerated remaining =>
    simp only [notFixed, Bool.false_eq_true, ↓reduceIte] at headFits bodyFits
    refine ⟨⟨true, child, childGenerated, Or.inl rfl, rfl, fun _ => rfl, Nat.le_refl _, by omega⟩,
      by omega, by omega,
      ⟨remainingFront, remainingBack, remaining, rfl, ?_, by omega, by omega, host⟩⟩
    intro other equality
    cases equality
    exact notFixed

/-- Fixed field heads remain before the variable body region, while variable
fields advance the body only after their four-byte offset head is initialized. -/
theorem table_field_child (name : String) (desc : Desc) (fields : List (String × Desc))
    (value : Value) (values : List Value) (child : Plan) (plans : List Plan)
    (capacity head body : Nat)
    (h : TableInvariant (.fields ((name, desc) :: fields)) (value :: values)
      (child :: plans) capacity head body) :
    SszX86.CodecEmit.GeneratedCall desc value (some child) child.size.value ∧
      if FixedSize.isFixed desc then
        head + child.size.value ≤ body ∧
          TableInvariant (.fields fields) values plans capacity (head + child.size.value) body
      else
        head + 4 ≤ body ∧ body + child.size.value ≤ capacity ∧
          TableInvariant (.fields fields) values plans capacity (head + 4) (body + child.size.value) := by
  rcases h with ⟨front, back, generated, arity, variable, headFits, bodyFits, host⟩
  have tailArity : Parts.arity (.fields fields) values = true := by
    simpa [Parts.arity] using arity
  have tailVariable : ∀ element, Parts.fields fields = .repeated element →
      FixedSize.isFixed element = false := by intro element equality; cases equality
  cases generated with
  | fields name desc fields value values keep child plans remainingFront remainingBack childGenerated remaining =>
    cases fixed : FixedSize.isFixed desc with
    | true =>
      simp only [fixed, ↓reduceIte, Nat.zero_add] at headFits bodyFits ⊢
      refine ⟨⟨true, child, childGenerated, Or.inl rfl, rfl, fun _ => rfl,
        Nat.le_refl _, by omega⟩, by omega,
        ⟨remainingFront, remainingBack, remaining, tailArity, tailVariable, by omega, bodyFits, host⟩⟩
    | false =>
      simp only [fixed, Bool.false_eq_true, ↓reduceIte] at headFits bodyFits ⊢
      refine ⟨⟨true, child, childGenerated, Or.inl rfl, rfl, fun _ => rfl,
        Nat.le_refl _, by omega⟩, by omega, by omega,
        ⟨remainingFront, remainingBack, remaining, tailArity, tailVariable, by omega, by omega, host⟩⟩

end SszX86.CodecEmitParts

import SszX86.CodecEmitInvariant

set_option autoImplicit false

namespace SszX86.CodecEmitParts
open SszNative
open SszNative.Codec (Desc Value)
open SszNative.CodecMeasure (Plan Parts)

/-- Successful measurement makes the native min(value_count, plan_count) an
exact traversal of both arrays. Field exhaustion is excluded by arity, not by
an assumed future loop result. -/
theorem generated_count (parts : Parts) (values : List Value) (keep : Bool)
    (plans : List Plan) (front back : Nat)
    (generated : SszNative.CodecEmit.GeneratedChildren parts values keep plans front back)
    (arity : parts.arity values = true) : plans.length = values.length := by
  induction generated with
  | nil => rfl
  | exhausted => simp [Parts.arity] at arity
  | repeated element value values keep child plans front back generated remaining ih =>
    simp only [List.length_cons, ih rfl]
  | fields name desc fields value values keep child plans front back generated remaining ih =>
    have tail : Parts.arity (.fields fields) values = true := by
      simpa [Parts.arity] using arity
    simp only [List.length_cons, ih tail]

/-- The sequential native loop emits unplanned fixed children into suffixes;
its size is the exact sum of those children, never an empty zip over plans. -/
structure SequentialInvariant (parts : Parts) (values : List Value)
    (capacity position : Nat) where
  plans : List Plan
  front : Nat
  back : Nat
  generated : SszNative.CodecEmit.GeneratedChildren parts values false plans front back
  arity : parts.arity values = true
  fixed : parts.allFixed = true
  fits : position + front + back ≤ capacity
  host : capacity < 2 ^ 64

/-- Independent head and body cursors describe disjoint retained fixed heads
and variable bodies. The entire remaining head fits before the body cursor. -/
structure TableInvariant (parts : Parts) (values : List Value) (plans : List Plan)
    (capacity head body : Nat) where
  front : Nat
  back : Nat
  generated : SszNative.CodecEmit.GeneratedChildren parts values true plans front back
  arity : parts.arity values = true
  repeatedVariable : ∀ element, parts = .repeated element → FixedSize.isFixed element = false
  headFits : head + front ≤ body
  bodyFits : body + back ≤ capacity
  host : capacity < 2 ^ 64

theorem TableInvariant.count {parts : Parts} {values : List Value} {plans : List Plan}
    {capacity head body : Nat} (h : TableInvariant parts values plans capacity head body) :
    min plans.length values.length = values.length := by
  rw [generated_count parts values true plans h.front h.back h.generated h.arity]
  exact Nat.min_self _

/-- Native branch selection is represented by facts about the original supplied
plan. Empty variable collections take the sequential zero-iteration path. -/
inductive StartInvariant (parts : Parts) (values : List Value) (supplied : Option Plan)
    (capacity size : Nat) where
  | empty (valuesEmpty : values = [])
      (childrenEmpty : SszNative.CodecEmit.children supplied = []) (zero : size = 0) :
      StartInvariant parts values supplied capacity size
  | sequential (h : SequentialInvariant parts values capacity 0)
      (childrenEmpty : SszNative.CodecEmit.children supplied = [])
      (size : size = h.front + h.back) : StartInvariant parts values supplied capacity size
  | table (plans : List Plan) (nonempty : plans ≠ [])
      (h : TableInvariant parts values plans capacity 0 (SszNative.CodecEmit.leading supplied))
      (children : SszNative.CodecEmit.children supplied = plans)
      (size : size = SszNative.CodecEmit.leading supplied + h.back) :
      StartInvariant parts values supplied capacity size

private theorem composite_unique {desc : Desc} {first second : Parts}
    (hfirst : SszNative.CodecEmit.Composite desc first)
    (hsecond : SszNative.CodecEmit.Composite desc second) : first = second := by
  cases hfirst <;> cases hsecond <;> rfl

/-- The actual measured-plan invariant determines every private loop-mode
premise, including discarded fixed descendants and the empty variable case. -/
theorem generated_start (desc : Desc) (parts : Parts) (values : List Value)
    (supplied : Option Plan) (capacity : Nat)
    (shape : SszNative.CodecEmit.Composite desc parts)
    (call : SszX86.CodecEmit.GeneratedCall desc (.seq values) supplied capacity) :
    StartInvariant parts values supplied capacity call.measured.size.value := by
  have usable := call.usable
  have children := call.children
  have sameLeading := call.leading
  have fits := call.fits
  have host := call.host
  cases generated : call.generated with
  | primitive primitive value retain size expected => cases shape
  | parts desc actualParts values retain plan plans front back actualShape arity generated
      size frontSize retained =>
    have same := composite_unique actualShape shape
    subst actualParts
    have available : retain = true ∨ parts.allFixed = true :=
      usable.imp_right (SszNative.CodecEmit.composite_fixed desc parts shape)
    by_cases fixed : parts.allFixed = true
    · have keep : (retain && !parts.allFixed) = false := by simp [fixed]
      rw [keep] at generated retained
      have noChildren : SszNative.CodecEmit.children supplied = [] := by
        simpa only [Bool.false_eq_true, ↓reduceIte] using children.trans retained
      exact .sequential ⟨plans, front, back, generated, arity, fixed, by omega, host⟩
        noChildren size
    · have notFixed : parts.allFixed = false := by cases equal : parts.allFixed <;> simp_all
      have retainTrue : retain = true := available.resolve_right fixed
      have keep : (retain && !parts.allFixed) = true := by simp [retainTrue, notFixed]
      rw [keep] at generated retained
      have actual : SszNative.CodecEmit.children supplied = plans := by
        simpa only [↓reduceIte] using children.trans retained
      cases plans with
      | nil =>
        have empty := SszNative.CodecEmit.generatedChildren_empty parts values true []
          front back generated arity rfl
        subst values
        cases generated
        exact .empty rfl actual (by simpa only [Nat.zero_add] using size)
      | cons child plans =>
        have nonempty : plan.children ≠ [] := by rw [retained]; simp
        have leading : SszNative.CodecEmit.leading supplied = front :=
          (sameLeading nonempty).trans frontSize
        refine .table (child :: plans) (by simp)
          ⟨front, back, generated, arity, ?_, by omega, by omega, host⟩ actual ?_
        · intro element equality
          subst parts
          exact notFixed
        · omega

end SszX86.CodecEmitParts

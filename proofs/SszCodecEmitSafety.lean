import SszCodecEmitPlans

set_option autoImplicit false

namespace SszNative.CodecEmit

open Codec (Desc Value)
open CodecMeasure (Plan Parts)

theorem bind_result_ok {α β : Type} {first : Emitted α} {next : α → Emitted β}
    {value : α} (success : first.result = .ok value) :
    (bind first next).result = (next value).result := by
  simp only [bind, success]

theorem sub_success (out : Slice) (start count : Nat) (fits : start + count ≤ out.length) :
    (sub out start count).result = .ok ⟨out.address + start, count⟩ := by
  simp only [sub, fits, ↓reduceIte, pure]

theorem suffix_success (out : Slice) (start : Nat) (fits : start ≤ out.length) :
    (suffix out start).result = .ok ⟨out.address + start, out.length - start⟩ := by
  simp only [suffix, fits, ↓reduceIte, pure]

theorem copy_success (out : Slice) (bytes : Ssz.Bytes) (fits : bytes.size ≤ out.length) :
    (copy out bytes).result = .ok bytes.size := by
  simp only [copy, fits, ↓reduceIte]

theorem hostSize_success (size : NatOperand) (used : Nat) (host : size.value < 2 ^ 64) :
    (CodecMeasure.hostSize size used).result = .ok size.value := by
  simp only [CodecMeasure.hostSize, Serialize.hostSize, host, ↓reduceIte,
    Serialize.unchanged, Except.mapError]

theorem returned_success {α : Type} {result : Except Codec.Error α} {value : α}
    (success : result = .ok value) : (returned result).result = .ok value := by
  simp only [returned, success, Except.mapError]

/-- Primitive semantic success supplies both the exact copy length and, for
uint, the width needed by the private emitter's separate host conversion. -/
theorem primitive_emit_success (shape : Serialize.Desc) (value : Value) (size : Nat)
    (out : Slice) (semantic : Serialize.expectedSize shape value.toPrimitive = .ok size)
    (fits : size ≤ out.length) (host : out.length < 2 ^ 64) :
    (primitive shape value out).result = .ok size := by
  have emitted := (Serialize.expected_encoding shape value.toPrimitive).2 size semantic
  have copied : (copy out (Serialize.emit shape value.toPrimitive)).result = .ok size := by
    rw [copy_success out _ (by rw [emitted]; exact fits), emitted]
  cases shape <;> cases value <;> try exact copied
  all_goals try { simp [Value.toPrimitive, Serialize.expectedSize] at semantic }
  rename_i width number
  have widthSize : width.value = size := by
    simp only [Value.toPrimitive, Serialize.expectedSize] at semantic
    split at semantic
    · exact Except.ok.inj semantic
    · cases semantic
  rw [primitive, bind_result_ok (returned_success
    (hostSize_success width 0 (by omega)))]
  exact copied

theorem composite_fixed (desc : Desc) (parts : Parts) (shape : Composite desc parts)
    (fixed : FixedSize.isFixed desc = true) : parts.allFixed = true := by
  cases shape <;> simp_all only [FixedSize.isFixed, Parts.allFixed, Bool.false_eq_true]

/-- Fixed descendants need no retained runtime plan, even when measured with
retain=false by an all-fixed ancestor. -/
theorem generated_fixed_children (desc : Desc) (value : Value) (retain : Bool)
    (plan : Plan) (generated : Generated desc value retain plan)
    (fixed : FixedSize.isFixed desc = true) : plan.children = [] := by
  cases generated with
  | primitive => rfl
  | parts desc parts values retain plan plans front back shape arity generated size leading children =>
    have allFixed := composite_fixed desc parts shape fixed
    simpa only [allFixed, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      using children
  | union => simp only [FixedSize.isFixed, Bool.false_eq_true] at fixed

theorem generatedChildren_empty (parts : Parts) (values : List Value) (keep : Bool)
    (plans : List Plan) (front back : Nat)
    (generated : GeneratedChildren parts values keep plans front back)
    (arity : parts.arity values = true) (empty : plans = []) : values = [] := by
  cases generated with
  | nil => rfl
  | exhausted => simp [Parts.arity] at arity
  | repeated => cases empty
  | fields => cases empty

/-- The recursive hypothesis is local to actual value children; no assertion
about a future traversal or output buffer is stored in Generated. -/
def VisitSafe (values : List Value) (visit : Visit values) : Prop :=
  ∀ value member desc retain plan supplied out,
    Generated desc value retain plan →
    (retain = true ∨ FixedSize.isFixed desc = true) →
    children supplied = plan.children →
    (plan.children ≠ [] → leading supplied = plan.leading) →
    plan.size.value ≤ out.length → out.length < 2 ^ 64 →
    (visit value member desc supplied out).result = .ok plan.size.value

theorem sequential_generated_success (parts : Parts) (values : List Value)
    (visit : Visit values) (safe : VisitSafe values visit)
    (plans : List Plan) (front back : Nat)
    (generated : GeneratedChildren parts values false plans front back)
    (arity : parts.arity values = true) (fixed : parts.allFixed = true)
    (out : Slice) (position : Nat)
    (fits : position + front + back ≤ out.length) (host : out.length < 2 ^ 64) :
    (sequential parts values visit out position).result = .ok (position + front + back) := by
  induction values generalizing parts plans front back position with
  | nil =>
    cases generated
    simp only [sequential, pure, Nat.add_zero]
  | cons value values ih =>
    cases generated with
    | exhausted => simp [Parts.arity] at arity
    | repeated element value values keep child plans front back generated remaining =>
      have childFixed : FixedSize.isFixed element = true := fixed
      have childEmpty := generated_fixed_children element value false child generated childFixed
      simp only [childFixed, ↓reduceIte, Nat.zero_add] at fits ⊢
      have childRun := safe value (by simp) element false child none
        ⟨out.address + position, out.length - position⟩ generated (Or.inr childFixed)
        (by simpa only [children] using childEmpty.symm)
        (by intro nonempty; exact False.elim (nonempty childEmpty))
        (by dsimp; omega) (by dsimp; omega)
      rw [sequential, bind_result_ok (show (nextPart (.repeated element)).result =
        .ok (element, .repeated element) from rfl),
        bind_result_ok (suffix_success out position (by omega)), bind_result_ok childRun]
      have tailRun := ih (.repeated element) _
        (fun value member desc retain plan supplied out generated usable sameChildren sameLeading fits host =>
          safe value (List.mem_cons_of_mem _ member) desc retain plan supplied out generated usable
            sameChildren sameLeading fits host)
        plans front back remaining (by rfl) fixed (position + child.size.value) (by omega)
      simpa only [Nat.add_assoc] using tailRun
    | fields name desc fields value values keep child plans front back generated remaining =>
      have both : FixedSize.isFixed desc = true ∧ Parts.allFixed (.fields fields) = true := by
        simpa only [Parts.allFixed, FixedSize.fieldsFixed, Bool.and_eq_true] using fixed
      have tailArity : Parts.arity (.fields fields) values = true := by
        simpa [Parts.arity] using arity
      have childEmpty := generated_fixed_children desc value false child generated both.1
      simp only [both.1, ↓reduceIte, Nat.zero_add] at fits ⊢
      have childRun := safe value (by simp) desc false child none
        ⟨out.address + position, out.length - position⟩ generated (Or.inr both.1)
        (by simpa only [children] using childEmpty.symm)
        (by intro nonempty; exact False.elim (nonempty childEmpty))
        (by dsimp; omega) (by dsimp; omega)
      rw [sequential, bind_result_ok (show (nextPart (.fields ((name, desc) :: fields))).result =
        .ok (desc, .fields fields) from rfl),
        bind_result_ok (suffix_success out position (by omega)), bind_result_ok childRun]
      have tailRun := ih (.fields fields) _
        (fun value member desc retain plan supplied out generated usable sameChildren sameLeading fits host =>
          safe value (List.mem_cons_of_mem _ member) desc retain plan supplied out generated usable
            sameChildren sameLeading fits host)
        plans front back remaining tailArity both.2 (position + child.size.value) (by omega)
      simpa only [Nat.add_assoc] using tailRun

/-- A table advances separate head/body cursors. Repeated descriptors enter
this loop only when their element is variable; fields may mix both kinds. -/
theorem table_generated_success (parts : Parts) (values : List Value)
    (visit : Visit values) (safe : VisitSafe values visit)
    (plans : List Plan) (front back : Nat)
    (generated : GeneratedChildren parts values true plans front back)
    (arity : parts.arity values = true)
    (repeatedVariable : ∀ element, parts = .repeated element → FixedSize.isFixed element = false)
    (out : Slice) (head body : Nat)
    (headFits : head + front ≤ body) (bodyFits : body + back ≤ out.length)
    (host : out.length < 2 ^ 64) :
    (table parts values visit plans out head body).result = .ok (body + back) := by
  induction values generalizing parts plans front back head body with
  | nil =>
    cases generated
    simp only [table, pure, Nat.add_zero]
  | cons value values ih =>
    cases generated with
    | exhausted => simp [Parts.arity] at arity
    | repeated element value values keep child plans front back generated remaining =>
      have notFixed := repeatedVariable element rfl
      simp only [notFixed, Bool.false_eq_true, ↓reduceIte] at headFits bodyFits ⊢
      have childHost : child.size.value < 2 ^ 64 := by omega
      have childRun := safe value (by simp) element true child (some child)
        ⟨out.address + body, child.size.value⟩ generated (Or.inl rfl) rfl
        (by intro _; rfl) (Nat.le_refl _) childHost
      rw [table, bind_result_ok (show (nextPart (.repeated element)).result =
        .ok (element, .repeated element) from rfl),
        bind_result_ok (returned_success (hostSize_success child.size 0 childHost))]
      simp only [inline, Bool.false_eq_true, ↓reduceIte]
      rw [bind_result_ok (sub_success out head 4 (by omega)),
        bind_result_ok (copy_success ⟨out.address + head, 4⟩ (Ssz.uintBytes 4 body)
          (by simp only [Ssz.uintBytes_size, Nat.le_refl])),
        bind_result_ok (sub_success out body child.size.value (by omega)),
        bind_result_ok childRun]
      have tailRun := ih (.repeated element) _
        (fun value member desc retain plan supplied out generated usable sameChildren sameLeading fits host =>
          safe value (List.mem_cons_of_mem _ member) desc retain plan supplied out generated usable
            sameChildren sameLeading fits host)
        plans front back remaining (by rfl) (by intro other equal; cases equal; exact notFixed)
        (head + 4) (body + child.size.value) (by omega) (by omega)
      simpa only [Nat.add_assoc] using tailRun
    | fields name desc fields value values keep child plans front back generated remaining =>
      have tailArity : Parts.arity (.fields fields) values = true := by
        simpa [Parts.arity] using arity
      have tailVariable : ∀ element, Parts.fields fields = .repeated element →
          FixedSize.isFixed element = false := by intro element equal; cases equal
      cases fixed : FixedSize.isFixed desc with
      | false =>
        simp only [fixed, Bool.false_eq_true, ↓reduceIte] at headFits bodyFits ⊢
        have childHost : child.size.value < 2 ^ 64 := by omega
        have childRun := safe value (by simp) desc true child (some child)
          ⟨out.address + body, child.size.value⟩ generated (Or.inl rfl) rfl
          (by intro _; rfl) (Nat.le_refl _) childHost
        rw [table, bind_result_ok (show (nextPart (.fields ((name, desc) :: fields))).result =
          .ok (desc, .fields fields) from rfl),
          bind_result_ok (returned_success (hostSize_success child.size 0 childHost))]
        simp only [inline, fixed, Bool.false_eq_true, ↓reduceIte]
        rw [bind_result_ok (sub_success out head 4 (by omega)),
          bind_result_ok (copy_success ⟨out.address + head, 4⟩ (Ssz.uintBytes 4 body)
            (by simp only [Ssz.uintBytes_size, Nat.le_refl])),
          bind_result_ok (sub_success out body child.size.value (by omega)),
          bind_result_ok childRun]
        have tailRun := ih (.fields fields) _
          (fun value member desc retain plan supplied out generated usable sameChildren sameLeading fits host =>
            safe value (List.mem_cons_of_mem _ member) desc retain plan supplied out generated usable
              sameChildren sameLeading fits host)
          plans front back remaining tailArity tailVariable
          (head + 4) (body + child.size.value) (by omega) (by omega)
        simpa only [Nat.add_assoc] using tailRun
      | true =>
        simp only [fixed, ↓reduceIte, Nat.zero_add] at headFits bodyFits ⊢
        have childHost : child.size.value < 2 ^ 64 := by omega
        have childRun := safe value (by simp) desc true child (some child)
          ⟨out.address + head, child.size.value⟩ generated (Or.inl rfl) rfl
          (by intro _; rfl) (Nat.le_refl _) childHost
        rw [table, bind_result_ok (show (nextPart (.fields ((name, desc) :: fields))).result =
          .ok (desc, .fields fields) from rfl),
          bind_result_ok (returned_success (hostSize_success child.size 0 childHost))]
        simp only [inline, fixed, ↓reduceIte]
        rw [bind_result_ok (sub_success out head child.size.value (by omega)),
          bind_result_ok childRun]
        exact ih (.fields fields) _
          (fun value member desc retain plan supplied out generated usable sameChildren sameLeading fits host =>
            safe value (List.mem_cons_of_mem _ member) desc retain plan supplied out generated usable
              sameChildren sameLeading fits host)
          plans front back remaining tailArity tailVariable
          (head + child.size.value) body (by omega) bodyFits

/-- Selection of the sequential or zip loop follows actual retained children,
including the zero-values case where a variable schema has an empty plan. -/
theorem emitParts_generated_success (parts : Parts) (values : List Value)
    (visit : Visit values) (safe : VisitSafe values visit) (retain : Bool)
    (plan : Plan) (plans : List Plan) (front back : Nat)
    (generated : GeneratedChildren parts values (retain && !parts.allFixed) plans front back)
    (arity : parts.arity values = true) (usable : retain = true ∨ parts.allFixed = true)
    (size : plan.size.value = front + back) (frontSize : plan.leading = front)
    (retained : plan.children = if retain && !parts.allFixed then plans else [])
    (supplied : Option Plan) (sameChildren : children supplied = plan.children)
    (sameLeading : plan.children ≠ [] → leading supplied = plan.leading)
    (out : Slice) (fits : plan.size.value ≤ out.length) (host : out.length < 2 ^ 64) :
    (emitParts parts values visit supplied out).result = .ok plan.size.value := by
  by_cases fixed : parts.allFixed = true
  · have keep : (retain && !parts.allFixed) = false := by simp only [fixed, Bool.not_true, Bool.and_false]
    rw [keep] at generated retained
    have noChildren : children supplied = [] := by simpa only [Bool.false_eq_true, ↓reduceIte] using sameChildren.trans retained
    rw [emitParts, noChildren]
    simp only [List.isEmpty_nil, ↓reduceIte]
    have run := sequential_generated_success parts values visit safe plans front back generated arity fixed
      out 0 (by omega) host
    simpa only [Nat.zero_add, ← size] using run
  · have notFixed : parts.allFixed = false := by cases equal : parts.allFixed <;> simp_all
    have retainedTrue : retain = true := usable.resolve_right fixed
    have keep : (retain && !parts.allFixed) = true := by simp only [retainedTrue, notFixed, Bool.not_false, Bool.and_true]
    rw [keep] at generated retained
    have actual : children supplied = plans := by simpa only [↓reduceIte] using sameChildren.trans retained
    cases plans with
    | nil =>
      have empty := generatedChildren_empty parts values true [] front back generated arity rfl
      subst values
      cases generated
      have zero : plan.size.value = 0 := by simpa only [Nat.zero_add] using size
      simp only [emitParts, actual, List.isEmpty_nil, ↓reduceIte, sequential, pure, zero]
    | cons child plans =>
      have nonempty : plan.children ≠ [] := by rw [retained]; simp
      have leadingSize : leading supplied = front := (sameLeading nonempty).trans frontSize
      rw [emitParts, actual]
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, leadingSize]
      rw [size]
      exact table_generated_success parts values visit safe (child :: plans) front back generated arity
        (by intro element equal; subst parts; exact notFixed) out 0 front (by omega) (by omega) host

/-- Private emit cannot fault and returns the measured size. Usability admits
nonretained fixed children and an absent supplied plan whenever no children
were retained; no future execution is assumed. -/
theorem generated_emit_success (desc : Desc) (value : Value) (retain : Bool)
    (plan : Plan) (supplied : Option Plan) (out : Slice)
    (generated : Generated desc value retain plan)
    (usable : retain = true ∨ FixedSize.isFixed desc = true)
    (sameChildren : children supplied = plan.children)
    (sameLeading : plan.children ≠ [] → leading supplied = plan.leading)
    (fits : plan.size.value ≤ out.length) (host : out.length < 2 ^ 64) :
    (emit desc value supplied out).result = .ok plan.size.value := by
  rw [emit]
  have safe : VisitSafe value.children
      (fun child _ desc supplied out => emit desc child supplied out) := by
    intro child member desc retain plan supplied out generated usable sameChildren sameLeading fits host
    exact generated_emit_success desc child retain plan supplied out generated usable sameChildren
      sameLeading fits host
  cases generated with
  | primitive shape value retain size semantic =>
    exact primitive_emit_success shape value size.value out semantic fits host
  | parts desc parts values retain plan plans front back shape arity generated size frontSize retained =>
    have available : retain = true ∨ parts.allFixed = true := usable.imp_right (composite_fixed desc parts shape)
    have run := emitParts_generated_success parts values _ safe retain plan plans front back generated
      arity available size frontSize retained supplied sameChildren sameLeading out fits host
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
    have childLeading : child.children ≠ [] → leading ((children supplied).head?) = child.leading := by
      intro nonempty
      rw [sameChildren, retained, retainedTrue]
      cases empty : child.children with
      | nil => exact False.elim (nonempty empty)
      | cons first rest => simp only [List.isEmpty_cons, Bool.not_false, Bool.and_true,
          ↓reduceIte, List.head?, leading]
    have childRun := safe value (by simp [Value.children]) chosen retain child
      ((children supplied).head?) ⟨out.address + 1, out.length - 1⟩ generated
      (Or.inl retainedTrue) childChildren childLeading (by dsimp; omega) (by dsimp; omega)
    rw [emitStep, bind_result_ok (copy_success out #[UInt8.ofNat selector.value] (by simp; omega)),
      bind_result_ok (returned_success option),
      bind_result_ok (suffix_success out 1 (by omega)), bind_result_ok childRun]
    simp only [pure, size, Nat.add_comm]
termination_by value.nesting
decreasing_by exact Value.child_nesting_lt _ _ (by assumption)

/-- The public caller needs only successful actual measurement, physical input,
and the host/output guards; Generated and retention witnesses are internal. -/
theorem measure_emit_success (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (physical : value.Physical) (plan : Plan)
    (measured : (CodecMeasure.measure desc value arena true).result = .ok plan)
    (out : Slice) (fits : plan.size.value ≤ out.length) (host : out.length < 2 ^ 64) :
    (emit desc value (some plan) out).result = .ok plan.size.value :=
  generated_emit_success desc value true plan (some plan) out
    (measure_generated desc value arena true physical plan measured) (Or.inl rfl) rfl
    (fun _ => rfl) fits host

end SszNative.CodecEmit

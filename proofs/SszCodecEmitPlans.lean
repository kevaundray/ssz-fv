import SszCodecEmit
import SszCodecMeasureProofs

set_option autoImplicit false

namespace SszNative.CodecEmit

open Codec (Desc Value Error)
open CodecMeasure (Plan Parts Partial Outcome)

/-- The five composite descriptor cases share the same native parts loop. -/
inductive Composite : Desc → Parts → Prop where
  | vector (element : Desc) (length : NatOperand) :
      Composite (.vector element length) (.repeated element)
  | list (element : Desc) (limit : NatOperand) :
      Composite (.list element limit) (.repeated element)
  | progressiveList (element : Desc) (limit : Option NatOperand) :
      Composite (.progressiveList element limit) (.repeated element)
  | container (fields : List (String × Desc)) :
      Composite (.container fields) (.fields fields)
  | progressiveContainer (active : List Bool) (fields : List (String × Desc)) :
      Composite (.progressiveContainer active fields) (.fields fields)

mutual
/-- Structural information justified by past successful measurement. There is
no premise about a future emitter execution, scratch capacity, or output memory.
Discarded children remain logical witnesses, never replacement runtime plans. -/
inductive Generated : Desc → Value → Bool → Plan → Prop where
  | primitive (shape : Serialize.Desc) (value : Value) (retain : Bool) (size : NatOperand)
      (semantic : Serialize.expectedSize shape value.toPrimitive = .ok size.value) :
      Generated (.primitive shape) value retain (Plan.leaf size)
  | parts (desc : Desc) (parts : Parts) (values : List Value) (retain : Bool)
      (plan : Plan) (plans : List Plan) (front back : Nat)
      (shape : Composite desc parts)
      (arity : parts.arity values = true)
      (generated : GeneratedChildren parts values (retain && !parts.allFixed) plans front back)
      (size : plan.size.value = front + back)
      (leading : plan.leading = front)
      (children : plan.children = if retain && !parts.allFixed then plans else []) :
      Generated desc (.seq values) retain plan
  | union (variants : List (NatOperand × Desc)) (selector : NatOperand) (value : Value)
      (retain : Bool) (chosen : Desc) (child plan : Plan)
      (option : CodecMeasure.option variants selector = .ok chosen)
      (generated : Generated chosen value retain child)
      (size : plan.size.value = child.size.value + 1)
      (children : plan.children = if retain && !child.children.isEmpty then [child] else []) :
      Generated (.compatibleUnion variants) (.union selector value) retain plan

/-- Paired-prefix evidence is intentionally allowed to stop on an exhausted
fields slice. The separate successful arity check excludes that case publicly. -/
inductive GeneratedChildren : Parts → List Value → Bool → List Plan → Nat → Nat → Prop where
  | nil (parts : Parts) (keep : Bool) : GeneratedChildren parts [] keep [] 0 0
  | exhausted (value : Value) (rest : List Value) (keep : Bool) :
      GeneratedChildren (.fields []) (value :: rest) keep [] 0 0
  | repeated (element : Desc) (value : Value) (values : List Value) (keep : Bool)
      (child : Plan) (plans : List Plan) (front back : Nat)
      (generated : Generated element value keep child)
      (remaining : GeneratedChildren (.repeated element) values keep plans front back) :
      GeneratedChildren (.repeated element) (value :: values) keep (child :: plans)
        ((if FixedSize.isFixed element then child.size.value else 4) + front)
        ((if FixedSize.isFixed element then 0 else child.size.value) + back)
  | fields (name : String) (desc : Desc) (fields : List (String × Desc))
      (value : Value) (values : List Value) (keep : Bool)
      (child : Plan) (plans : List Plan) (front back : Nat)
      (generated : Generated desc value keep child)
      (remaining : GeneratedChildren (.fields fields) values keep plans front back) :
      GeneratedChildren (.fields ((name, desc) :: fields)) (value :: values) keep (child :: plans)
        ((if FixedSize.isFixed desc then child.size.value else 4) + front)
        ((if FixedSize.isFixed desc then 0 else child.size.value) + back)
end

theorem measure_bind_ok {α β : Type} (first : Outcome α) (next : α → Nat → Outcome β)
    (result : β) :
    (CodecMeasure.bind first next).result = .ok result ↔
      ∃ value, first.result = .ok value ∧ (next value first.used).result = .ok result := by
  cases equation : first.result <;> simp [CodecMeasure.bind, equation]

theorem refines_success {α β : Type} (project : α → β) (result : Except Error α)
    (expected : Except Ssz.Err β) (value : α)
    (refines : CodecMeasure.Refines project result expected) (success : result = .ok value) :
    expected = .ok (project value) := by
  rcases refines with correct | scratch | output
  · simpa only [success, Except.map, Codec.eraseResult, Except.ok.injEq] using correct.symm
  · rw [success] at scratch
    cases scratch
  · rw [success] at output
    cases output

theorem accumulate_success (inline : Bool) (child : Plan) (totals : Partial)
    (arena : Delimited.ArenaState) (next : Partial)
    (success : (CodecMeasure.accumulate inline child totals arena).result = .ok next) :
    next.leading.value = totals.leading.value + (if inline then child.size.value else 4) ∧
      next.bodies.value = totals.bodies.value + (if inline then 0 else child.size.value) ∧
      next.children = totals.children := by
  have sizes := refines_success CodecMeasure.partialSize _ _ next
    (CodecMeasure.accumulate_refines inline child totals arena) success
  have numeric : next.leading.value = totals.leading.value +
      (if inline then child.size.value else 4) ∧
      next.bodies.value = totals.bodies.value + (if inline then 0 else child.size.value) := by
    cases inline <;> simpa [CodecMeasure.partialSize, Prod.mk.injEq] using sizes.symm
  refine ⟨numeric.1, numeric.2, ?_⟩
  unfold CodecMeasure.accumulate at success
  obtain ⟨front, _, success⟩ := (measure_bind_ok _ _ next).1 success
  cases inline with
  | true =>
    simp only [↓reduceIte, CodecMeasure.unchanged, Except.ok.injEq] at success
    subst next
    rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at success
    obtain ⟨back, _, success⟩ := (measure_bind_ok _ _ next).1 success
    simp only [CodecMeasure.unchanged, Except.ok.injEq] at success
    subst next
    rfl

/-- Successful traversal keeps every generated child when keep is true and
none otherwise; arithmetic metadata equals the actual paired-prefix sums. -/
theorem measureLoop_generated (parts : Parts) (values : List Value)
    (visit : CodecMeasure.Visit values)
    (correct : ∀ value member desc arena retain plan,
      (visit value member desc arena retain).result = .ok plan →
      Generated desc value retain plan)
    (keep : Bool) (allocation : Option Arena.Reservation) (index : Nat)
    (totals : Partial) (arena : Delimited.ArenaState) (result : Partial)
    (success : (CodecMeasure.measureLoop parts values visit keep allocation index totals arena).result =
      .ok result) :
    ∃ plans front back, GeneratedChildren parts values keep plans front back ∧
      result.leading.value = totals.leading.value + front ∧
      result.bodies.value = totals.bodies.value + back ∧
      result.children = totals.children ++ (if keep then plans else []) := by
  induction values generalizing parts index totals arena with
  | nil =>
    simp only [CodecMeasure.measureLoop, CodecMeasure.unchanged, Except.ok.injEq] at success
    subst result
    exact ⟨[], 0, 0, .nil parts keep, by omega, by omega, by cases keep <;> simp⟩
  | cons value rest ih =>
    have step (desc : Desc) (remaining : Parts)
        (make : ∀ child plans front back,
          Generated desc value keep child → GeneratedChildren remaining rest keep plans front back →
          GeneratedChildren parts (value :: rest) keep (child :: plans)
            ((if FixedSize.isFixed desc then child.size.value else 4) + front)
            ((if FixedSize.isFixed desc then 0 else child.size.value) + back))
        (run : (CodecMeasure.bind (visit value (by simp) desc arena keep) fun child used =>
          CodecMeasure.bind (CodecMeasure.accumulate (FixedSize.isFixed desc) child totals
            { arena with used := used }) fun next used =>
          CodecMeasure.bind (CodecMeasure.writePlan allocation index child used) fun _ used =>
          CodecMeasure.measureLoop remaining rest
            (fun value member => visit value (List.mem_cons_of_mem _ member)) keep allocation
            (index + 1) { next with children := if keep then next.children ++ [child] else next.children }
            { arena with used := used }).result = .ok result) :
        ∃ plans front back, GeneratedChildren parts (value :: rest) keep plans front back ∧
          result.leading.value = totals.leading.value + front ∧
          result.bodies.value = totals.bodies.value + back ∧
          result.children = totals.children ++ (if keep then plans else []) := by
      obtain ⟨child, measured, run⟩ := (measure_bind_ok _ _ result).1 run
      obtain ⟨next, accumulated, run⟩ := (measure_bind_ok _ _ result).1 run
      obtain ⟨completed, _, run⟩ := (measure_bind_ok _ _ result).1 run
      have sums := accumulate_success _ child totals _ next accumulated
      obtain ⟨plans, front, back, generated, first, second, retained⟩ :=
        ih (parts := remaining)
          (visit := fun value member => visit value (List.mem_cons_of_mem _ member))
          (correct := fun value member desc arena retain plan success =>
            correct value (List.mem_cons_of_mem _ member) desc arena retain plan success)
          (index := index + 1) (totals := _) (arena := _) run
      refine ⟨child :: plans,
        (if FixedSize.isFixed desc then child.size.value else 4) + front,
        (if FixedSize.isFixed desc then 0 else child.size.value) + back,
        make child plans front back (correct value (by simp) desc arena keep child measured) generated,
        ?_, ?_, ?_⟩
      · dsimp only at first
        omega
      · dsimp only at second
        omega
      · dsimp only at retained
        rw [retained, sums.2.2]
        cases keep <;> simp [List.append_assoc]
    cases parts with
    | repeated element =>
      refine step element (.repeated element)
        (fun child plans front back generated remaining =>
          .repeated element value rest keep child plans front back generated remaining) ?_
      simpa only [CodecMeasure.measureLoop] using success
    | fields fields =>
      cases fields with
      | nil =>
        simp only [CodecMeasure.measureLoop, CodecMeasure.unchanged, Except.ok.injEq] at success
        subst result
        exact ⟨[], 0, 0, .exhausted value rest keep, by omega, by omega,
          by cases keep <;> simp⟩
      | cons field fields =>
        rcases field with ⟨name, desc⟩
        refine step desc (.fields fields)
          (fun child plans front back generated remaining =>
            .fields name desc fields value rest keep child plans front back generated remaining) ?_
        simpa only [CodecMeasure.measureLoop] using success

theorem finishParts_success (parts : Parts) (values : List Value) (totals : Partial)
    (allocation : Option Arena.Reservation) (arena : Delimited.ArenaState) (plan : Plan)
    (success : (CodecMeasure.finishParts parts values totals allocation arena).result = .ok plan) :
    parts.arity values = true ∧ plan.size.value = totals.leading.value + totals.bodies.value ∧
      plan.leading = totals.leading.value ∧ plan.children = totals.children := by
  unfold CodecMeasure.finishParts at success
  split at success
  next arity =>
    obtain ⟨size, added, success⟩ := (measure_bind_ok _ _ plan).1 success
    obtain ⟨completed, _, success⟩ := (measure_bind_ok _ _ plan).1 success
    obtain ⟨leading, converted, success⟩ := (measure_bind_ok _ _ plan).1 success
    have total := refines_success NatOperand.value _ _ size
      (CodecMeasure.add_refines totals.leading totals.bodies arena) added
    have front := refines_success id _ _ leading
      (CodecMeasure.hostSize_refines totals.leading _) converted
    simp only [CodecMeasure.unchanged, Except.ok.injEq] at success
    subst plan
    simp only [Except.ok.injEq, id_eq] at total front
    exact ⟨arity, total.symm, front.symm, rfl⟩
  next arity =>
    simp only [CodecMeasure.unchanged] at success
    cases success

theorem measureParts_generated (desc : Desc) (parts : Parts) (values : List Value)
    (shape : Composite desc parts) (visit : CodecMeasure.Visit values)
    (correct : ∀ value member desc arena retain plan,
      (visit value member desc arena retain).result = .ok plan →
      Generated desc value retain plan)
    (arena : Delimited.ArenaState) (retain : Bool) (plan : Plan)
    (success : (CodecMeasure.measureParts parts values visit arena retain).result = .ok plan) :
    Generated desc (.seq values) retain plan := by
  have run (allocation : Option Arena.Reservation) (used : Nat)
      (success : (CodecMeasure.bind
        (CodecMeasure.measureLoop parts values visit (retain && !parts.allFixed) allocation 0
          CodecMeasure.initial { arena with used := used })
        (fun totals used => CodecMeasure.finishParts parts values totals allocation
          { arena with used := used })).result = .ok plan) :
      Generated desc (.seq values) retain plan := by
    obtain ⟨totals, loop, finished⟩ := (measure_bind_ok _ _ plan).1 success
    obtain ⟨plans, front, back, generated, first, second, children⟩ :=
      measureLoop_generated parts values visit correct _ allocation 0 CodecMeasure.initial _ totals loop
    have final := finishParts_success parts values totals allocation _ plan finished
    have zero : (NatOperand.small 0).value = 0 := rfl
    simp only [CodecMeasure.initial, zero, Nat.zero_add, List.nil_append] at first second children
    exact .parts desc parts values retain plan plans front back shape final.1 generated
      (by rw [final.2.1, first, second]) (by rw [final.2.2.1, first])
      (by rw [final.2.2.2, children])
  dsimp only [CodecMeasure.measureParts] at success
  split at success
  · obtain ⟨allocation, _, success⟩ := (measure_bind_ok _ _ plan).1 success
    exact run (some allocation) _ success
  · exact run none arena.used success

theorem unionPlan_children (child : Plan) (arena : Delimited.ArenaState) (retain : Bool)
    (plan : Plan) (success : (CodecMeasure.unionPlan child arena retain).result = .ok plan) :
    plan.children = if retain && !child.children.isEmpty then [child] else [] := by
  unfold CodecMeasure.unionPlan at success
  obtain ⟨size, _, success⟩ := (measure_bind_ok _ _ plan).1 success
  split at success
  next keep =>
    obtain ⟨allocation, _, success⟩ := (measure_bind_ok _ _ plan).1 success
    obtain ⟨completed, _, success⟩ := (measure_bind_ok _ _ plan).1 success
    simp only [CodecMeasure.unchanged, Except.ok.injEq] at success
    subst plan
    change [child] = if retain && !child.children.isEmpty then [child] else []
    simp only [keep, ↓reduceIte]
  next keep =>
    simp only [CodecMeasure.unchanged, Except.ok.injEq] at success
    subst plan
    change [] = if retain && !child.children.isEmpty then [child] else []
    simp only [keep]
    rfl

/-- Generated-plan evidence comes from the actual retained/nonretained run,
including nested allocation cursors. No plan is synthesized or remeasured. -/
theorem measure_generated (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (retain : Bool) (physical : value.Physical) (plan : Plan)
    (success : (CodecMeasure.measure desc value arena retain).result = .ok plan) :
    Generated desc value retain plan := by
  rw [CodecMeasure.measure] at success
  have visit (child : Value) (member : child ∈ value.children) (desc : Desc)
      (arena : Delimited.ArenaState) (retain : Bool) (plan : Plan)
      (success : (CodecMeasure.measure desc child arena retain).result = .ok plan) :
      Generated desc child retain plan :=
    measure_generated desc child arena retain (Value.physical_child value child physical member) plan success
  cases desc with
  | primitive shape =>
    change (CodecMeasure.primitive shape value arena).result = .ok plan at success
    have expected := refines_success (fun plan : Plan => plan.size.value) _ _ plan
      (CodecMeasure.primitive_refines shape value arena physical) success
    unfold CodecMeasure.primitive at success
    cases measured : (Serialize.measure shape value.toPrimitive arena).result with
    | error reason => simp only [measured, Except.map, Except.mapError] at success; cases success
    | ok size =>
      simp only [measured, Except.map, Except.mapError, Except.ok.injEq] at success
      subst plan
      exact .primitive shape value retain size expected
  | vector element length =>
    cases value with
    | seq values =>
      obtain ⟨completed, _, success⟩ := (measure_bind_ok _ _ plan).1 success
      exact measureParts_generated _ _ values (.vector element length) _ visit _ retain plan success
    | _ => cases success
  | list element limit =>
    cases value with
    | seq values =>
      obtain ⟨completed, _, success⟩ := (measure_bind_ok _ _ plan).1 success
      exact measureParts_generated _ _ values (.list element limit) _ visit _ retain plan success
    | _ => cases success
  | progressiveList element limit =>
    cases value with
    | seq values =>
      obtain ⟨completed, _, success⟩ := (measure_bind_ok _ _ plan).1 success
      exact measureParts_generated _ _ values (.progressiveList element limit) _ visit _ retain plan success
    | _ => cases success
  | container fields =>
    cases value with
    | seq values =>
      exact measureParts_generated _ _ values (.container fields) _ visit _ retain plan success
    | _ => cases success
  | progressiveContainer active fields =>
    cases value with
    | seq values =>
      exact measureParts_generated _ _ values (.progressiveContainer active fields) _ visit _ retain plan success
    | _ => cases success
  | compatibleUnion variants =>
    cases value with
    | union selector child =>
      obtain ⟨chosen, option, success⟩ := (measure_bind_ok _ _ plan).1 success
      obtain ⟨childPlan, measured, success⟩ := (measure_bind_ok _ _ plan).1 success
      have size := refines_success (fun plan : Plan => plan.size.value) _ _ plan
        (CodecMeasure.unionPlan_refines childPlan _ retain) success
      simp only [Except.ok.injEq] at size
      exact .union variants selector child retain chosen childPlan plan option
        (visit child (by simp [Value.children]) chosen _ retain childPlan measured)
        size.symm (unionPlan_children childPlan _ retain plan success)
    | _ => cases success
termination_by value.nesting
decreasing_by exact Value.child_nesting_lt _ _ member

end SszNative.CodecEmit

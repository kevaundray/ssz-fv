import SszCodecMeasureRefinement

set_option autoImplicit false

namespace SszNative.CodecMeasure

open Codec (Desc Value Error)

/-- The loop comparison quantifies over every actual callback cursor, so nested
allocations and earlier failed attempts are not replaced by a resource oracle. -/
theorem measureLoop_refines (parts : Parts) (values : List Value)
    (visit : Visit values) (expectedVisit : ExpectedVisit values)
    (visitCorrect : ∀ value member desc arena retain,
      Refines (fun plan => plan.size.value) (visit value member desc arena retain).result
        (expectedVisit value member desc))
    (keep : Bool) (allocation : Option Arena.Reservation) (index : Nat)
    (totals : Partial) (arena : Delimited.ArenaState) :
    Refines partialSize (measureLoop parts values visit keep allocation index totals arena).result
      (expectedLoop parts values expectedVisit totals.leading.value totals.bodies.value) := by
  induction values generalizing parts index totals arena with
  | nil =>
    rw [measureLoop, expectedLoop]
    exact Or.inl rfl
  | cons value rest ih =>
    cases parts with
    | repeated element =>
      rw [measureLoop, expectedLoop]
      dsimp only
      apply refines_bind (fun (plan : Plan) => plan.size.value) partialSize _ _ _ _
        (visitCorrect value (by simp) element arena keep)
      intro child used
      apply refines_bind partialSize partialSize _ _ _
        (fun sums => expectedLoop (.repeated element) rest
          (fun value member => expectedVisit value (List.mem_cons_of_mem _ member)) sums.1 sums.2)
        (accumulate_refines _ child totals { arena with used := used })
      intro next used
      apply refines_bind (fun _ => ()) partialSize _ _ _
        (fun _ => expectedLoop (.repeated element) rest
          (fun value member => expectedVisit value (List.mem_cons_of_mem _ member))
          next.leading.value next.bodies.value)
        (writePlan_refines allocation index child used)
      intro _ used
      apply ih
      intro child member desc childArena childRetain
      exact visitCorrect child (List.mem_cons_of_mem _ member) desc childArena childRetain
    | fields entries =>
      cases entries with
      | nil =>
        rw [measureLoop, expectedLoop]
        exact Or.inl rfl
      | cons field entries =>
        rcases field with ⟨name, desc⟩
        rw [measureLoop, expectedLoop]
        dsimp only
        apply refines_bind (fun (plan : Plan) => plan.size.value) partialSize _ _ _ _
          (visitCorrect value (by simp) desc arena keep)
        intro child used
        apply refines_bind partialSize partialSize _ _ _
          (fun sums => expectedLoop (.fields entries) rest
            (fun value member => expectedVisit value (List.mem_cons_of_mem _ member)) sums.1 sums.2)
          (accumulate_refines _ child totals { arena with used := used })
        intro next used
        apply refines_bind (fun _ => ()) partialSize _ _ _
          (fun _ => expectedLoop (.fields entries) rest
            (fun value member => expectedVisit value (List.mem_cons_of_mem _ member))
            next.leading.value next.bodies.value)
          (writePlan_refines allocation index child used)
        intro _ used
        apply ih
        intro child member childDesc childArena childRetain
        exact visitCorrect child (List.mem_cons_of_mem _ member) childDesc childArena childRetain

theorem finishParts_refines (parts : Parts) (values : List Value) (totals : Partial)
    (allocation : Option Arena.Reservation) (arena : Delimited.ArenaState) :
    Refines (fun plan => plan.size.value)
      (finishParts parts values totals allocation arena).result
      (if parts.arity values then expectedTotal (totals.leading.value + totals.bodies.value)
       else .error .typeMismatch) := by
  unfold finishParts
  split
  · apply refines_bind NatOperand.value (fun (plan : Plan) => plan.size.value) _ _ _
      expectedTotal (add_refines totals.leading totals.bodies arena)
    intro size used
    have comparison := compositeSize_refines size used
    unfold expectedTotal
    by_cases overflow : 2 ^ 32 ≤ size.value
    · simp only [overflow, ↓reduceIte] at comparison ⊢
      apply refines_bind (fun _ => ()) (fun (plan : Plan) => plan.size.value) _ _ _
        (fun _ => .ok size.value) comparison
      intro _ used
      apply refines_bind id (fun (plan : Plan) => plan.size.value) _ _ _
        (fun _ => .ok size.value) (hostSize_refines totals.leading used)
      intro leading used
      exact Or.inl rfl
    · simp only [overflow, ↓reduceIte] at comparison ⊢
      apply refines_bind (fun _ => ()) (fun (plan : Plan) => plan.size.value) _ _ _
        (fun _ => .ok size.value) comparison
      intro _ used
      apply refines_bind id (fun (plan : Plan) => plan.size.value) _ _ _
        (fun _ => .ok size.value) (hostSize_refines totals.leading used)
      intro leading used
      exact Or.inl rfl
  · exact Or.inl rfl

theorem measureParts_refines (parts : Parts) (values : List Value)
    (visit : Visit values) (expectedVisit : ExpectedVisit values)
    (visitCorrect : ∀ value member desc arena retain,
      Refines (fun plan => plan.size.value) (visit value member desc arena retain).result
        (expectedVisit value member desc))
    (arena : Delimited.ArenaState) (retain : Bool) :
    Refines (fun plan => plan.size.value) (measureParts parts values visit arena retain).result
      (expectedParts parts values expectedVisit) := by
  have run (allocation : Option Arena.Reservation) (used : Nat) :
      Refines (fun plan => plan.size.value)
        (bind (measureLoop parts values visit (retain && !parts.allFixed) allocation 0 initial
          { arena with used := used })
          (fun totals used => finishParts parts values totals allocation
            { arena with used := used })).result
        (expectedParts parts values expectedVisit) := by
    unfold expectedParts
    apply refines_bind partialSize (fun (plan : Plan) => plan.size.value) _ _ _ _
      (measureLoop_refines parts values visit expectedVisit visitCorrect
        (retain && !parts.allFixed) allocation 0 initial { arena with used := used })
    intro totals used
    exact finishParts_refines parts values totals allocation { arena with used := used }
  dsimp only [measureParts]
  split
  · apply refines_bind (fun _ => ()) (fun (plan : Plan) => plan.size.value) _ _ _
      (fun _ => expectedParts parts values expectedVisit)
      (reservePlans_refines (parts.paired values) arena)
    intro allocation used
    exact run (some allocation) used
  · exact run none arena.used

theorem option_refines (variants : List (NatOperand × Desc)) (selector : NatOperand)
    (used : Nat) :
    Refines id (unchanged used (option variants selector)).result
      (expectedOption variants selector) := by
  induction variants with
  | nil => exact Or.inl rfl
  | cons variant variants ih =>
    rcases variant with ⟨chosen, desc⟩
    unfold option expectedOption
    split
    · exact Or.inl rfl
    · exact ih

theorem bounded_refines_expected (limit : Option NatOperand) (actual : NatOperand) (used : Nat) :
    Refines (fun _ => ()) (bounded limit actual used).result
      (expectedBound limit actual.value) := by
  have same : Ssz.boundCheck (limit.map NatOperand.value) actual.value =
      expectedBound limit actual.value := by
    cases limit <;> rfl
  rw [← same]
  exact bounded_refines limit actual used

/-- Every declaration constructor and every wrong value kind is covered. The
only representation restriction is on physical value slices, not logical Nats. -/
theorem measureStep_refines (desc : Desc) (value : Value) (physical : value.Physical)
    (visit : Visit value.children) (expectedVisit : ExpectedVisit value.children)
    (visitCorrect : ∀ child member desc arena retain,
      Refines (fun plan => plan.size.value) (visit child member desc arena retain).result
        (expectedVisit child member desc))
    (arena : Delimited.ArenaState) (retain : Bool) :
    Refines (fun plan => plan.size.value) (measureStep desc value arena retain visit).result
      (expectedStep desc value expectedVisit) := by
  cases desc with
  | primitive shape => exact primitive_refines shape value arena physical
  | vector element length =>
    cases value with
    | seq values =>
      change values.length < 2 ^ 64 ∧ Value.listPhysical values at physical
      unfold measureStep expectedStep
      by_cases same : length.value = values.length
      · simp only [same, ↓reduceIte]
        have first := exact_refines length values.length arena.used physical.1
        simp only [same, ↓reduceIte] at first
        apply refines_bind (fun (_ : Unit) => ()) (fun (plan : Plan) => plan.size.value)
          _ _ (.ok ()) (fun _ => expectedParts (.repeated element) values expectedVisit) first
        intro _ used
        exact measureParts_refines _ _ visit expectedVisit visitCorrect { arena with used := used } retain
      · simp only [same, ↓reduceIte]
        have first := exact_refines length values.length arena.used physical.1
        simp only [same, ↓reduceIte] at first
        apply refines_bind (fun (_ : Unit) => ()) (fun (plan : Plan) => plan.size.value)
          _ _ (.error (.scope length.value values.length))
          (fun _ => expectedParts (.repeated element) values expectedVisit) first
        intro _ used
        exact measureParts_refines _ _ visit expectedVisit visitCorrect { arena with used := used } retain
    | _ => exact Or.inl rfl
  | list element limit =>
    cases value with
    | seq values =>
      change values.length < 2 ^ 64 ∧ Value.listPhysical values at physical
      unfold measureStep expectedStep
      apply refines_bind (fun _ => ()) (fun (plan : Plan) => plan.size.value) _ _ _ _
        (by simpa only [Serialize.count_value values.length physical.1] using
          bounded_refines_expected (some limit) (Serialize.count values.length) arena.used)
      intro _ used
      exact measureParts_refines _ _ visit expectedVisit visitCorrect { arena with used := used } retain
    | _ => exact Or.inl rfl
  | progressiveList element limit =>
    cases value with
    | seq values =>
      change values.length < 2 ^ 64 ∧ Value.listPhysical values at physical
      unfold measureStep expectedStep
      apply refines_bind (fun _ => ()) (fun (plan : Plan) => plan.size.value) _ _ _ _
        (by simpa only [Serialize.count_value values.length physical.1] using
          bounded_refines_expected limit (Serialize.count values.length) arena.used)
      intro _ used
      exact measureParts_refines _ _ visit expectedVisit visitCorrect { arena with used := used } retain
    | _ => exact Or.inl rfl
  | container fields =>
    cases value with
    | seq values => exact measureParts_refines _ _ visit expectedVisit visitCorrect arena retain
    | _ => exact Or.inl rfl
  | progressiveContainer active fields =>
    cases value with
    | seq values => exact measureParts_refines _ _ visit expectedVisit visitCorrect arena retain
    | _ => exact Or.inl rfl
  | compatibleUnion variants =>
    cases value with
    | union selector value =>
      unfold measureStep expectedStep
      apply refines_bind id (fun (plan : Plan) => plan.size.value) _ _ _ _
        (option_refines variants selector arena.used)
      intro chosen used
      apply refines_bind (fun (plan : Plan) => plan.size.value)
        (fun (plan : Plan) => plan.size.value) _ _ _ _
        (visitCorrect value (by simp [Value.children]) chosen { arena with used := used } retain)
      intro child used
      exact unionPlan_refines child { arena with used := used } retain
    | _ => exact Or.inl rfl

theorem measure_refines_expected (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (retain : Bool) (physical : value.Physical) :
    Refines (fun plan => plan.size.value) (measure desc value arena retain).result
      (expectedSize desc value) := by
  rw [measure, expectedSize]
  apply measureStep_refines desc value physical
  intro child member childDesc childArena childRetain
  exact measure_refines_expected childDesc child childArena childRetain
    (Value.physical_child value child physical member)
termination_by value.nesting
decreasing_by exact Value.child_nesting_lt _ _ member

/-- Full recursive pinned-serialization size refinement. Resource failure is an
explicit result alternative, and no trace/cursor field is erased from the model. -/
theorem measure_refines (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (retain : Bool) (physical : value.Physical) :
    Refines (fun plan => plan.size.value) (measure desc value arena retain).result
      ((Ssz.serialize desc.erase value.erase).map Array.size) := by
  rw [← expectedSize_eq_pinned]
  exact measure_refines_expected desc value arena retain physical

theorem encodedSize_refines (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (physical : value.Physical) :
    Refines id (encodedSize desc value arena).result
      ((Ssz.serialize desc.erase value.erase).map Array.size) := by
  unfold encodedSize
  have first := measure_refines desc value arena false physical
  have same (expected : Except Ssz.Err Nat) : expected.bind (fun size => .ok size) = expected := by
    cases expected <;> rfl
  rw [← same ((Ssz.serialize desc.erase value.erase).map Array.size)]
  apply refines_bind (fun (plan : Plan) => plan.size.value) id _ _ _ _ first
  intro plan used
  exact hostSize_refines plan.size used

theorem measure_success (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (retain : Bool) (physical : value.Physical) (plan : Plan)
    (success : (measure desc value arena retain).result = .ok plan) :
    (Ssz.serialize desc.erase value.erase).map Array.size = .ok plan.size.value := by
  rcases measure_refines desc value arena retain physical with correct | scratch | output
  · simpa only [success, Except.map, Codec.eraseResult, Except.ok.injEq] using correct.symm
  · rw [success] at scratch
    cases scratch
  · rw [success] at output
    cases output

theorem encodedSize_success (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (physical : value.Physical) (size : Nat)
    (success : (encodedSize desc value arena).result = .ok size) :
    (Ssz.serialize desc.erase value.erase).map Array.size = .ok size := by
  rcases encodedSize_refines desc value arena physical with correct | scratch | output
  · simpa only [success, Except.map, Codec.eraseResult, Except.ok.injEq, id_eq] using correct.symm
  · rw [success] at scratch
    cases scratch
  · rw [success] at output
    cases output

end SszNative.CodecMeasure

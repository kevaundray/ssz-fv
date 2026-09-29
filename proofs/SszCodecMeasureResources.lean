import SszCodecMeasureResourcesCore

set_option autoImplicit false

namespace SszNative.CodecMeasure

open Codec (Desc Value Error)

/-- Arithmetic and primitive calls remain visible; only Plan storage is excluded. -/
def PlanFreeEffect : Effect → Prop
  | .primitive _ _ _ _ | .arithmetic _ _ _ _ => True
  | .reservePlans _ _ _ | .writePlan _ _ _ => False

def PlanFree {α : Type} (outcome : Outcome α) : Prop :=
  ∀ effect ∈ outcome.effects, PlanFreeEffect effect

theorem unchanged_planFree {α : Type} (used : Nat) (result : Except Error α) :
    PlanFree (unchanged used result) := by
  simp [PlanFree, unchanged]

theorem planFree_of_effects_nil {α : Type} (outcome : Outcome α)
    (empty : outcome.effects = []) : PlanFree outcome := by
  intro effect member
  rw [empty] at member
  cases member

theorem bind_planFree {α β : Type} (first : Outcome α) (next : α → Nat → Outcome β)
    (freeFirst : PlanFree first) (freeNext : ∀ value used, PlanFree (next value used)) :
    PlanFree (bind first next) := by
  intro effect member
  cases result : first.result with
  | error reason => exact freeFirst effect (by simpa only [bind, result] using member)
  | ok value =>
    have either : effect ∈ first.effects ∨ effect ∈ (next value first.used).effects := by
      simpa only [bind, result, List.mem_append] using member
    exact either.elim (freeFirst effect) (freeNext value first.used effect)

theorem primitive_planFree (shape : Serialize.Desc) (value : Value)
    (arena : Delimited.ArenaState) : PlanFree (primitive shape value arena) := by
  simp [PlanFree, primitive, PlanFreeEffect]

theorem add_planFree (left right : NatOperand) (arena : Delimited.ArenaState) :
    PlanFree (add left right arena) := by
  simp [PlanFree, add, PlanFreeEffect]

theorem accumulate_planFree (inline : Bool) (child : Plan) (totals : Partial)
    (arena : Delimited.ArenaState) : PlanFree (accumulate inline child totals arena) := by
  unfold accumulate
  apply bind_planFree _ _ (add_planFree _ _ arena)
  intro leading used
  split
  · exact unchanged_planFree _ _
  · apply bind_planFree _ _ (add_planFree _ _ _)
    intro bodies used
    exact unchanged_planFree _ _

/-- No reservation or slot write can be hidden inside an unretained traversal. -/
theorem measureLoop_planFree (parts : Parts) (values : List Value) (visit : Visit values)
    (index : Nat) (totals : Partial) (arena : Delimited.ArenaState)
    (freeVisit : ∀ value member desc arena, PlanFree (visit value member desc arena false)) :
    PlanFree (measureLoop parts values visit false none index totals arena) := by
  induction values generalizing parts index totals arena with
  | nil =>
    rw [measureLoop]
    exact unchanged_planFree _ _
  | cons value rest ih =>
    cases parts with
    | repeated element =>
      simp only [measureLoop]
      apply bind_planFree _ _ (freeVisit value _ element arena)
      intro child used
      apply bind_planFree _ _ (accumulate_planFree _ _ _ _)
      intro next used
      apply bind_planFree _ _ (unchanged_planFree _ _)
      intro _checked used
      apply ih
      intro value member desc arena
      exact freeVisit value (List.mem_cons_of_mem _ member) desc arena
    | fields fields =>
      cases fields with
      | nil =>
        rw [measureLoop]
        exact unchanged_planFree _ _
      | cons field fields =>
        rcases field with ⟨name, desc⟩
        simp only [measureLoop]
        apply bind_planFree _ _ (freeVisit value _ desc arena)
        intro child used
        apply bind_planFree _ _ (accumulate_planFree _ _ _ _)
        intro next used
        apply bind_planFree _ _ (unchanged_planFree _ _)
        intro _checked used
        apply ih
        intro value member desc arena
        exact freeVisit value (List.mem_cons_of_mem _ member) desc arena

theorem finishParts_planFree (parts : Parts) (values : List Value) (totals : Partial)
    (allocation : Option Arena.Reservation) (arena : Delimited.ArenaState) :
    PlanFree (finishParts parts values totals allocation arena) := by
  unfold finishParts
  split
  · apply bind_planFree _ _ (add_planFree _ _ _)
    intro size used
    apply bind_planFree _ _
      (by simp only [PlanFree, (compositeSize_resources size used).2, List.not_mem_nil, false_implies, implies_true])
    intro _checked used
    apply bind_planFree _ _
      (by simp only [PlanFree, (hostSize_resources totals.leading used).2, List.not_mem_nil, false_implies, implies_true])
    intro leading used
    exact unchanged_planFree _ _
  · exact unchanged_planFree _ _

theorem measureParts_planFree (parts : Parts) (values : List Value) (visit : Visit values)
    (arena : Delimited.ArenaState)
    (freeVisit : ∀ value member desc arena, PlanFree (visit value member desc arena false)) :
    PlanFree (measureParts parts values visit arena false) := by
  simp only [measureParts, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  apply bind_planFree _ _ (measureLoop_planFree _ _ _ _ _ _ freeVisit)
  intro totals used
  exact finishParts_planFree _ _ _ _ _

theorem unionPlan_planFree (child : Plan) (arena : Delimited.ArenaState) :
    PlanFree (unionPlan child arena false) := by
  unfold unionPlan
  apply bind_planFree _ _ (add_planFree _ _ _)
  intro size used
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  exact unchanged_planFree _ _

theorem measureStep_planFree (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (visit : Visit value.children)
    (freeVisit : ∀ child member desc arena, PlanFree (visit child member desc arena false)) :
    PlanFree (measureStep desc value arena false visit) := by
  cases desc <;> cases value <;> simp only [measureStep]
  all_goals first
    | exact primitive_planFree _ _ _
    | exact unchanged_planFree _ _
    | exact measureParts_planFree _ _ _ _ freeVisit
    | (apply bind_planFree _ _
         (planFree_of_effects_nil _ (exactCount_resources _ _ _).2)
       intro _checked used
       exact measureParts_planFree _ _ _ _ freeVisit)
    | (apply bind_planFree _ _
         (planFree_of_effects_nil _ (bounded_resources _ _ _).2)
       intro _checked used
       exact measureParts_planFree _ _ _ _ freeVisit)
    | (apply bind_planFree _ _ (unchanged_planFree _ _)
       intro chosen used
       apply bind_planFree _ _ (freeVisit _ _ chosen { arena with used := used })
       intro child used
       exact unionPlan_planFree child { arena with used := used })

/-- This excludes attempted reservations too, even on a later failed execution. -/
theorem measure_planFree (desc : Desc) (value : Value) (arena : Delimited.ArenaState) :
    PlanFree (measure desc value arena false) := by
  rw [measure]
  apply measureStep_planFree
  intro child _member desc arena
  exact measure_planFree desc child arena
termination_by value.nesting
decreasing_by exact Value.child_nesting_lt _ _ (by assumption)

theorem measure_no_reservePlans (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (count : Nat) (site : Delimited.ArenaState) (reservation : Option Arena.Reservation) :
    Effect.reservePlans count site reservation ∉ (measure desc value arena false).effects := by
  intro member
  exact measure_planFree desc value arena _ member

theorem measure_no_writePlan (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (address index : Nat) (plan : Plan) :
    Effect.writePlan address index plan ∉ (measure desc value arena false).effects := by
  intro member
  exact measure_planFree desc value arena _ member

theorem encodedSize_planFree (desc : Desc) (value : Value) (arena : Delimited.ArenaState) :
    PlanFree (encodedSize desc value arena) := by
  intro effect member
  rw [(encodedSize_resources desc value arena).2] at member
  exact measure_planFree desc value arena effect member

/-- A result invariant imposes no successful-execution premise on a callback. -/
def Ensures {α : Type} (post : α → Prop) (outcome : Outcome α) : Prop :=
  ∀ value, outcome.result = .ok value → post value

theorem ensures_true {α : Type} (outcome : Outcome α) : Ensures (fun _ => True) outcome :=
  fun _ _ => True.intro

theorem ensures_mono {α : Type} (first second : α → Prop) (outcome : Outcome α)
    (holds : Ensures first outcome) (implies : ∀ value, first value → second value) :
    Ensures second outcome := fun value success => implies value (holds value success)

theorem unchanged_ensures {α : Type} (post : α → Prop) (used : Nat) (value : α)
    (holds : post value) : Ensures post (unchanged used (.ok value)) := by
  intro actual success
  cases success
  exact holds

theorem error_ensures {α : Type} (post : α → Prop) (used : Nat) (reason : Error) :
    Ensures post (unchanged used (.error reason)) := by
  intro actual impossible
  cases impossible

theorem bind_ensures {α β : Type} (post : α → Prop) (result : β → Prop)
    (first : Outcome α) (next : α → Nat → Outcome β)
    (firstPost : Ensures post first)
    (nextPost : ∀ value used, post value → Ensures result (next value used)) :
    Ensures result (bind first next) := by
  intro actual success
  cases firstResult : first.result with
  | error reason => simp only [bind, firstResult] at success; cases success
  | ok value =>
    exact nextPost value first.used (firstPost value firstResult) actual
      (by simpa only [bind, firstResult] using success)

theorem accumulate_children (inline : Bool) (child : Plan) (totals : Partial)
    (arena : Delimited.ArenaState) :
    Ensures (fun (next : Partial) => next.children = totals.children) (accumulate inline child totals arena) := by
  unfold accumulate
  refine bind_ensures (β := Partial) (fun _ => True) _ _ _ (ensures_true _) ?_
  intro leading used _
  split
  · exact unchanged_ensures _ _ _ rfl
  · refine bind_ensures (β := Partial) (fun _ => True) _ _ _ (ensures_true _) ?_
    intro bodies used _
    exact unchanged_ensures _ _ _ rfl

/-- A successful paired-prefix loop retains exactly one child per pair when keep
is true, and preserves the original child list verbatim when keep is false. -/
theorem measureLoop_children (parts : Parts) (values : List Value) (visit : Visit values)
    (keep : Bool) (allocation : Option Arena.Reservation) (index : Nat)
    (totals : Partial) (arena : Delimited.ArenaState) :
    Ensures (fun (final : Partial) =>
      final.children.length = totals.children.length + (if keep then parts.paired values else 0) ∧
      (keep = false → final.children = totals.children))
      (measureLoop parts values visit keep allocation index totals arena) := by
  induction values generalizing parts index totals arena with
  | nil =>
    rw [measureLoop]
    refine unchanged_ensures _ _ _ ?_
    cases parts <;> cases keep <;> simp [Parts.paired]
  | cons value rest ih =>
    cases parts with
    | repeated element =>
      simp only [measureLoop]
      refine bind_ensures (β := Partial) (fun _ => True) _ _ _ (ensures_true _) ?_
      intro child used _
      refine bind_ensures (β := Partial) _ _ _ _ (accumulate_children _ _ _ _) ?_
      intro next used children
      refine bind_ensures (β := Partial) (fun _ => True) _ _ _ (ensures_true _) ?_
      intro _checked used _
      refine ensures_mono _ _ _ (ih _ _ _ _ _) ?_
      intro final holds
      cases keep <;>
        simp_all [Parts.paired, List.length_append, List.length_cons, Nat.add_assoc] <;> omega
    | fields fields =>
      cases fields with
      | nil =>
        rw [measureLoop]
        refine unchanged_ensures _ _ _ ?_
        cases keep <;> simp [Parts.paired]
      | cons field fields =>
        rcases field with ⟨name, desc⟩
        simp only [measureLoop]
        refine bind_ensures (β := Partial) (fun _ => True) _ _ _ (ensures_true _) ?_
        intro child used _
        refine bind_ensures (β := Partial) _ _ _ _ (accumulate_children _ _ _ _) ?_
        intro next used children
        refine bind_ensures (β := Partial) (fun _ => True) _ _ _ (ensures_true _) ?_
        intro _checked used _
        refine ensures_mono _ _ _ (ih _ _ _ _ _) ?_
        intro final holds
        cases keep with
        | false => simpa [children] using holds
        | true =>
          simp only [↓reduceIte, List.length_append, List.length_cons,
            List.length_nil, children, Parts.paired] at holds ⊢
          constructor
          · have count := holds.1
            omega
          · intro impossible
            cases impossible

theorem measureLoop_child_count (parts : Parts) (values : List Value) (visit : Visit values)
    (keep : Bool) (allocation : Option Arena.Reservation) (index : Nat)
    (totals final : Partial) (arena : Delimited.ArenaState)
    (success : (measureLoop parts values visit keep allocation index totals arena).result = .ok final) :
    final.children.length = totals.children.length + (if keep then parts.paired values else 0) :=
  (measureLoop_children parts values visit keep allocation index totals arena final success).1

theorem finishParts_children (parts : Parts) (values : List Value) (totals : Partial)
    (allocation : Option Arena.Reservation) (arena : Delimited.ArenaState) :
    Ensures (fun (plan : Plan) => plan.children = totals.children ∧ plan.allocation = allocation)
      (finishParts parts values totals allocation arena) := by
  unfold finishParts
  split
  · refine bind_ensures (β := Plan) (fun _ => True) _ _ _ (ensures_true _) ?_
    intro size used _
    refine bind_ensures (β := Plan) (fun _ => True) _ _ _ (ensures_true _) ?_
    intro _checked used _
    refine bind_ensures (β := Plan) (fun _ => True) _ _ _ (ensures_true _) ?_
    intro leading used _
    exact unchanged_ensures _ _ _ ⟨rfl, rfl⟩
  · exact error_ensures _ _ _

/-- Child count is exact even for the empty retained reservation. The non-retained
branch has no allocation; keep is the native retain-and-not-all-fixed guard. -/
theorem measureParts_children (parts : Parts) (values : List Value) (visit : Visit values)
    (arena : Delimited.ArenaState) (retain : Bool) :
    Ensures (fun (plan : Plan) =>
      plan.children.length = (if retain && !parts.allFixed then parts.paired values else 0) ∧
      ((retain && !parts.allFixed) = false → plan.children = [] ∧ plan.allocation = none))
      (measureParts parts values visit arena retain) := by
  unfold measureParts
  dsimp only
  split
  · rename_i keep
    refine bind_ensures (β := Plan) (fun _ => True) _ _ _ (ensures_true _) ?_
    intro allocation used _
    refine bind_ensures (β := Plan) _ _ _ _ (measureLoop_children _ _ _ _ _ _ _ _) ?_
    intro totals used children
    refine ensures_mono _ _ _ (finishParts_children _ _ _ _ _) ?_
    intro plan fields
    constructor
    · rw [fields.1]
      simpa only [initial, List.length_nil, Nat.zero_add, keep, ↓reduceIte] using children.1
    · intro notKeep
      simp only [notKeep, Bool.false_eq_true] at keep
  · rename_i notKeep
    refine bind_ensures (β := Plan) _ _ _ _ (measureLoop_children _ _ _ _ _ _ _ _) ?_
    intro totals used children
    refine ensures_mono _ _ _ (finishParts_children _ _ _ _ _) ?_
    intro plan fields
    constructor
    · rw [fields.1]
      simpa only [initial, List.length_nil, Nat.zero_add, notKeep, Bool.false_eq_true,
        ↓reduceIte] using children.1
    · intro keepFalse
      exact ⟨fields.1.trans (children.2 keepFalse), fields.2⟩

/-- Root plan emptiness does not assume anything about callback results. -/
theorem measureParts_nonretained (parts : Parts) (values : List Value) (visit : Visit values)
    (arena : Delimited.ArenaState) :
    Ensures (fun (plan : Plan) => plan.children = [] ∧ plan.allocation = none)
      (measureParts parts values visit arena false) := by
  intro plan success
  exact (measureParts_children parts values visit arena false plan success).2 rfl

theorem primitive_nonretained (shape : Serialize.Desc) (value : Value)
    (arena : Delimited.ArenaState) :
    Ensures (fun (plan : Plan) => plan.children = [] ∧ plan.allocation = none)
      (primitive shape value arena) := by
  intro plan success
  cases measured : (Serialize.measure shape value.toPrimitive arena).result with
  | error reason => simp only [primitive, measured, Except.map, Except.mapError] at success; cases success
  | ok size =>
    simp only [primitive, measured, Except.map, Except.mapError] at success
    cases success
    exact ⟨rfl, rfl⟩

theorem unionPlan_nonretained (child : Plan) (arena : Delimited.ArenaState) :
    Ensures (fun (plan : Plan) => plan.children = [] ∧ plan.allocation = none)
      (unionPlan child arena false) := by
  unfold unionPlan
  refine bind_ensures (β := Plan) (fun _ => True) _ _ _ (ensures_true _) ?_
  intro size used _
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  exact unchanged_ensures _ _ _ ⟨rfl, rfl⟩

theorem measureStep_nonretained (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (visit : Visit value.children) :
    Ensures (fun (plan : Plan) => plan.children = [] ∧ plan.allocation = none)
      (measureStep desc value arena false visit) := by
  cases desc <;> cases value <;> simp only [measureStep]
  all_goals first
    | exact primitive_nonretained _ _ _
    | exact error_ensures _ _ _
    | exact measureParts_nonretained _ _ _ _
    | (refine bind_ensures (β := Plan) (fun _ => True) _ _ _ (ensures_true _) ?_
       intro _checked used _
       exact measureParts_nonretained _ _ _ _)
    | (refine bind_ensures (β := Plan) (fun _ => True) _ _ _ (ensures_true _) ?_
       intro chosen used _
       refine bind_ensures (β := Plan) (fun _ => True) _ _ _ (ensures_true _) ?_
       intro child used _
       exact unionPlan_nonretained _ _)

theorem measure_nonretained (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (plan : Plan) (success : (measure desc value arena false).result = .ok plan) :
    plan.children = [] ∧ plan.allocation = none := by
  rw [measure] at success
  exact measureStep_nonretained desc value arena _ plan success

theorem add_value (left right : NatOperand) (arena : Delimited.ArenaState) :
    Ensures (fun (size : NatOperand) => size.value = left.value + right.value) (add left right arena) := by
  intro size success
  cases called : (NatAdd.run left right arena.base arena.capacity arena.used).result with
  | error reason =>
    simp only [add, called, Except.mapError] at success
    cases success
  | ok actual =>
    simp only [add, called, Except.mapError] at success
    cases success
    exact NatAdd.run_value left right arena.base arena.capacity arena.used _ called

theorem hostSize_value (size : NatOperand) (used : Nat) :
    Ensures (fun (actual : Nat) => actual = size.value) (hostSize size used) := by
  intro actual success
  unfold hostSize Serialize.hostSize at success
  split at success
  · cases success
    rfl
  · cases success

theorem compositeSize_bound (size : NatOperand) (used : Nat) :
    Ensures (fun _ => size.value < 2 ^ 32) (compositeSize size used) := by
  intro _checked success
  unfold compositeSize at success
  split at success
  · cases success
  · omega

/-- A successful composite has the exact unbounded sum, a correctly narrowed
leading width, and the final offset-domain bound. No early bound is assumed. -/
theorem finishParts_bounds (parts : Parts) (values : List Value) (totals : Partial)
    (allocation : Option Arena.Reservation) (arena : Delimited.ArenaState) :
    Ensures (fun (plan : Plan) => plan.leading = totals.leading.value ∧
      plan.size.value = totals.leading.value + totals.bodies.value ∧
      plan.size.value < 2 ^ 32)
      (finishParts parts values totals allocation arena) := by
  unfold finishParts
  split
  · refine bind_ensures (β := Plan) _ _ _ _ (add_value _ _ _) ?_
    intro size used sum
    refine bind_ensures (β := Plan) _ _ _ _ (compositeSize_bound size used) ?_
    intro _checked used bound
    refine bind_ensures (β := Plan) _ _ _ _ (hostSize_value totals.leading used) ?_
    intro leading used narrowed
    exact unchanged_ensures _ _ _ ⟨narrowed, sum, bound⟩
  · exact error_ensures _ _ _

theorem measureParts_bounds (parts : Parts) (values : List Value) (visit : Visit values)
    (arena : Delimited.ArenaState) (retain : Bool) :
    Ensures (fun (plan : Plan) => plan.leading ≤ plan.size.value ∧ plan.size.value < 2 ^ 32)
      (measureParts parts values visit arena retain) := by
  have finish (totals : Partial) (allocation : Option Arena.Reservation)
      (atArena : Delimited.ArenaState) :
      Ensures (fun (plan : Plan) => plan.leading ≤ plan.size.value ∧ plan.size.value < 2 ^ 32)
        (finishParts parts values totals allocation atArena) := by
    refine ensures_mono _ _ _ (finishParts_bounds parts values totals allocation atArena) ?_
    intro plan bounds
    exact ⟨by rw [bounds.1, bounds.2.1]; omega, bounds.2.2⟩
  unfold measureParts
  dsimp only
  split
  · refine bind_ensures (β := Plan) (fun _ => True) _ _ _ (ensures_true _) ?_
    intro allocation used _
    refine bind_ensures (β := Plan) (fun _ => True) _ _ _ (ensures_true _) ?_
    intro totals used _
    exact finish _ _ _
  · refine bind_ensures (β := Plan) (fun _ => True) _ _ _ (ensures_true _) ?_
    intro totals used _
    exact finish _ _ _

theorem reservePlans_allocation (count : Nat) (arena : Delimited.ArenaState) :
    Ensures (fun (allocation : Arena.Reservation) =>
      Arena.reserve arena.base arena.capacity arena.used (5 * count) = some allocation)
      (reservePlans count arena) := by
  intro allocation success
  unfold reservePlans at success
  dsimp only at success
  split at success
  · cases success
  · rename_i actual reserved
    cases success
    exact reserved

/-- A retained composite's reservation is the original pre-child attempt, not
some later nested allocation. Its slot count is the paired-prefix count. -/
theorem measureParts_retained_allocation (parts : Parts) (values : List Value)
    (visit : Visit values) (arena : Delimited.ArenaState) (retain : Bool)
    (keep : (retain && !parts.allFixed) = true) :
    Ensures (fun (plan : Plan) => ∃ allocation,
      plan.allocation = some allocation ∧
      Arena.reserve arena.base arena.capacity arena.used (5 * parts.paired values) =
        some allocation)
      (measureParts parts values visit arena retain) := by
  simp only [measureParts, keep, ↓reduceIte]
  refine bind_ensures (β := Plan) _ _ _ _ (reservePlans_allocation _ _) ?_
  intro allocation used reserved
  refine bind_ensures (β := Plan) (fun _ => True) _ _ _ (ensures_true _) ?_
  intro totals used _
  refine ensures_mono _ _ _ (finishParts_children _ _ _ _ _) ?_
  intro plan fields
  exact ⟨allocation, fields.2, reserved⟩

/-- The complete reservation attempt is the first visible effect, regardless of
failure, arity mismatch, empty input, or any later child/arithmetic outcome. -/
theorem measureParts_reservation_first (parts : Parts) (values : List Value)
    (visit : Visit values) (arena : Delimited.ArenaState) (retain : Bool)
    (keep : (retain && !parts.allFixed) = true) :
    ∃ suffix, (measureParts parts values visit arena retain).effects =
      Effect.reservePlans (parts.paired values) arena
        (Arena.reserve arena.base arena.capacity arena.used (5 * parts.paired values)) :: suffix := by
  cases reserved : Arena.reserve arena.base arena.capacity arena.used
      (5 * parts.paired values) with
  | none =>
    refine ⟨[], ?_⟩
    simp only [measureParts, keep, ↓reduceIte, reservePlans, reserved, bind]
  | some allocation =>
    simp only [measureParts, keep, ↓reduceIte, reservePlans, reserved, bind,
      List.singleton_append]
    exact ⟨_, rfl⟩

theorem primitive_leading (shape : Serialize.Desc) (value : Value)
    (arena : Delimited.ArenaState) :
    Ensures (fun (plan : Plan) => plan.leading = 0) (primitive shape value arena) := by
  intro plan success
  cases measured : (Serialize.measure shape value.toPrimitive arena).result with
  | error reason =>
    simp only [primitive, measured, Except.map, Except.mapError] at success
    cases success
  | ok size =>
    simp only [primitive, measured, Except.map, Except.mapError] at success
    cases success
    rfl

theorem unionPlan_leading (child : Plan) (arena : Delimited.ArenaState) (retain : Bool) :
    Ensures (fun (plan : Plan) => plan.leading = 0) (unionPlan child arena retain) := by
  unfold unionPlan
  refine bind_ensures (β := Plan) (fun _ => True) _ _ _ (ensures_true _) ?_
  intro size used _
  split
  · refine bind_ensures (β := Plan) (fun _ => True) _ _ _ (ensures_true _) ?_
    intro allocation used _
    refine bind_ensures (β := Plan) (fun _ => True) _ _ _ (ensures_true _) ?_
    intro _checked used _
    exact unchanged_ensures _ _ _ rfl
  · exact unchanged_ensures _ _ _ rfl

theorem measureStep_leading_le_size (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (retain : Bool) (visit : Visit value.children) :
    Ensures (fun (plan : Plan) => plan.leading ≤ plan.size.value)
      (measureStep desc value arena retain visit) := by
  have primitiveBound (shape : Serialize.Desc) (value : Value) :
      Ensures (fun (plan : Plan) => plan.leading ≤ plan.size.value) (primitive shape value arena) := by
    refine ensures_mono _ _ _ (primitive_leading shape value arena) ?_
    intro plan leading
    rw [leading]
    exact Nat.zero_le _
  have partsBound (parts : Parts) (values : List Value) (visit : Visit values)
      (atArena : Delimited.ArenaState) :
      Ensures (fun (plan : Plan) => plan.leading ≤ plan.size.value)
        (measureParts parts values visit atArena retain) :=
    ensures_mono _ _ _ (measureParts_bounds parts values visit atArena retain)
      (fun _ bounds => bounds.1)
  cases desc <;> cases value <;> simp only [measureStep]
  all_goals first
    | exact primitiveBound _ _
    | exact error_ensures _ _ _
    | exact partsBound _ _ _ _
    | (refine bind_ensures (β := Plan) (fun _ => True) _ _ _ (ensures_true _) ?_
       intro _checked used _
       exact partsBound _ _ _ _)
    | (refine bind_ensures (β := Plan) (fun _ => True) _ _ _ (ensures_true _) ?_
       intro chosen used _
       refine bind_ensures (β := Plan) (fun _ => True) _ _ _ (ensures_true _) ?_
       intro child used _
       refine ensures_mono _ _ _ (unionPlan_leading child _ retain) ?_
       intro plan leading
       rw [leading]
       exact Nat.zero_le _)

theorem measure_leading_le_size (desc : Desc) (value : Value)
    (arena : Delimited.ArenaState) (retain : Bool) (plan : Plan)
    (success : (measure desc value arena retain).result = .ok plan) :
    plan.leading ≤ plan.size.value := by
  rw [measure] at success
  exact measureStep_leading_le_size desc value arena retain _ plan success

end SszNative.CodecMeasure

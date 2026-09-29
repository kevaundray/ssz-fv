import SszIndicesFrontierResourcesMonotone

set_option autoImplicit false

namespace SszNative.Indices

/-- The proof view of the final in-place ordering operation; it has no arena
allocation and is reached only after every initializer has completed. -/
def frontierOrder (sorted : Bool) (values : List NatOperand) : List NatOperand :=
  if sorted then values.mergeSort (fun left right => right.value ≤ left.value) else values

def finishFrontier (sorted : Bool) (reservation : Arena.Reservation)
    (fill : Outcome (List NatOperand × Nat)) : Outcome NatSlice :=
  bind fill fun result cursor =>
    if sorted then
      ⟨.ok ⟨frontierOrder sorted result.1, reservation⟩, cursor,
        [.sorted reservation.pointer (frontierOrder sorted result.1)]⟩
    else unchanged cursor (.ok ⟨result.1, reservation⟩)

@[simp] theorem frontierOrder_length (sorted : Bool) (values : List NatOperand) :
    (frontierOrder sorted values).length = values.length := by
  cases sorted <;> simp only [frontierOrder, Bool.false_eq_true, ↓reduceIte, List.length_mergeSort]

/-- Complete public execution certificate. Refusal has no allocation. A failed
reservation records its attempt and unchanged cursor. The only allocating branch
records the full outer reservation before the actual initialized-prefix trace. -/
inductive FrontierRun (base capacity used : Nat) (sorted : Bool) : Outcome NatSlice → Prop where
  | refused (reason : Error) : FrontierRun base capacity used sorted (unchanged used (.error reason))
  | exhausted (count : Nat)
      (failed : TypedArena.reserve natLayout base capacity used count = none) :
      FrontierRun base capacity used sorted
        ⟨.error scratch, used, [.reserve natLayout count used none]⟩
  | reserved (count : Nat) (reservation : Arena.Reservation)
      (fill : Outcome (List NatOperand × Nat))
      (reserved : TypedArena.reserve natLayout base capacity used count = some reservation)
      (initializedPrefix : FrontierPrefix reservation 0 count fill) :
      FrontierRun base capacity used sorted
        ⟨(finishFrontier sorted reservation fill).result,
          (finishFrontier sorted reservation fill).used,
          .reserve natLayout count used (some reservation) ::
            (finishFrontier sorted reservation fill).effects⟩

private theorem bind_success_frame {α β : Type} (value : α) (cursor : Nat)
    (effects : List Effect) (next : α → Nat → Outcome β) :
    bind ⟨.ok value, cursor, effects⟩ next =
      ⟨(next value cursor).result, (next value cursor).used,
        effects ++ (next value cursor).effects⟩ := rfl

theorem pathIndices_resources (index : NatOperand) (base capacity used : Nat) :
    FrontierRun base capacity used false (pathIndices index base capacity used) := by
  cases measured : length index with
  | error reason =>
    simpa only [pathIndices, measured, unchanged, bind] using
      FrontierRun.refused (base := base) (capacity := capacity) (used := used) (sorted := false) reason
  | ok count =>
    by_cases wide : count ≥ 2^64
    · simpa only [pathIndices, measured, bind_unchanged, wide, ↓reduceIte] using
        FrontierRun.refused (base := base) (capacity := capacity) (used := used) (sorted := false) scratch
    · cases reserved : TypedArena.reserve natLayout base capacity used count with
      | none =>
        simp only [pathIndices, measured, bind_unchanged, wide, ↓reduceIte]
        simpa only [reserveNats, reserved, bind_error] using
          FrontierRun.exhausted (base := base) (capacity := capacity) (used := used)
            (sorted := false) count reserved
      | some reservation =>
        let fill := fillLevels reservation (fun _ => true)
          (fun level cursor => arithmetic cursor (NatShift.shr index level base capacity cursor))
          count 0 0 reservation.used
        have initializedPrefix : FrontierPrefix reservation 0 count fill := by
          simpa only [retainedLevels_all] using fillLevels_prefix reservation (fun _ => true)
            (fun level cursor => arithmetic cursor (NatShift.shr index level base capacity cursor))
            count 0 0 reservation.used
        have certified := FrontierRun.reserved (base := base) (capacity := capacity)
          (used := used) (sorted := false) count reservation fill reserved initializedPrefix
        simp only [pathIndices, measured, bind_unchanged, wide, ↓reduceIte]
        simp only [reserveNats, reserved, bind_success_frame, List.singleton_append]
        simpa only [finishFrontier, Bool.false_eq_true, ↓reduceIte] using certified

theorem branchIndices_resources (index : NatOperand) (base capacity used : Nat) :
    FrontierRun base capacity used false (branchIndices index base capacity used) := by
  cases measured : length index with
  | error reason =>
    simpa only [branchIndices, measured, unchanged, bind] using
      FrontierRun.refused (base := base) (capacity := capacity) (used := used) (sorted := false) reason
  | ok count =>
    by_cases wide : count ≥ 2^64
    · simpa only [branchIndices, measured, bind_unchanged, wide, ↓reduceIte] using
        FrontierRun.refused (base := base) (capacity := capacity) (used := used) (sorted := false) scratch
    · cases reserved : TypedArena.reserve natLayout base capacity used count with
      | none =>
        simp only [branchIndices, measured, bind_unchanged, wide, ↓reduceIte]
        simpa only [reserveNats, reserved, bind_error] using
          FrontierRun.exhausted (base := base) (capacity := capacity) (used := used)
            (sorted := false) count reserved
      | some reservation =>
        let fill := fillLevels reservation (fun _ => true)
          (fun level cursor => shiftXor index level true base capacity cursor)
          count 0 0 reservation.used
        have initializedPrefix : FrontierPrefix reservation 0 count fill := by
          simpa only [retainedLevels_all] using fillLevels_prefix reservation (fun _ => true)
            (fun level cursor => shiftXor index level true base capacity cursor)
            count 0 0 reservation.used
        have certified := FrontierRun.reserved (base := base) (capacity := capacity)
          (used := used) (sorted := false) count reservation fill reserved initializedPrefix
        simp only [branchIndices, measured, bind_unchanged, wide, ↓reduceIte]
        simp only [reserveNats, reserved, bind_success_frame, List.singleton_append]
        simpa only [finishFrontier, Bool.false_eq_true, ↓reduceIte] using certified

theorem collectPathIndices_resources (indices : List NatOperand) (base capacity used : Nat) :
    FrontierRun base capacity used false (collectPathIndices indices base capacity used) := by
  cases counted : countPaths indices 0 with
  | error reason =>
    simpa only [collectPathIndices, counted, unchanged, bind] using
      FrontierRun.refused (base := base) (capacity := capacity) (used := used) (sorted := false) reason
  | ok count =>
    cases reserved : TypedArena.reserve natLayout base capacity used count with
    | none =>
      simp only [collectPathIndices, counted, bind_unchanged]
      simpa only [reserveNats, reserved, bind_error] using
        FrontierRun.exhausted (base := base) (capacity := capacity) (used := used)
          (sorted := false) count reserved
    | some reservation =>
      let fill := fillClaims indices false reservation base capacity indices 0 0 reservation.used
      have countEq : count = retainedClaims indices false indices 0 := by
        simpa only [Nat.zero_add] using countPaths_count indices indices 0 0 count counted
      have initializedPrefix : FrontierPrefix reservation 0 count fill := by
        rw [countEq]
        exact fillClaims_prefix indices false reservation base capacity indices 0 0 reservation.used
      have certified := FrontierRun.reserved (base := base) (capacity := capacity)
        (used := used) (sorted := false) count reservation fill reserved initializedPrefix
      simp only [collectPathIndices, counted, bind_unchanged]
      simp only [reserveNats, reserved, bind_success_frame, List.singleton_append]
      simpa only [finishFrontier, Bool.false_eq_true, ↓reduceIte] using certified

theorem helperIndices_resources (indices : List NatOperand) (base capacity used : Nat) :
    FrontierRun base capacity used true (helperIndices indices base capacity used) := by
  cases validated : rejectRelated indices with
  | error reason =>
    simpa only [helperIndices, validated, unchanged, bind] using
      FrontierRun.refused (base := base) (capacity := capacity) (used := used) (sorted := true) reason
  | ok accepted =>
    cases accepted
    cases counted : countHelpers indices indices 0 0 with
    | error reason =>
      simp only [helperIndices, validated, bind_unchanged, counted]
      simpa only [unchanged, bind_error] using
        FrontierRun.refused (base := base) (capacity := capacity) (used := used) (sorted := true) reason
    | ok count =>
      cases reserved : TypedArena.reserve natLayout base capacity used count with
      | none =>
        simp only [helperIndices, validated, counted, bind_unchanged]
        simpa only [reserveNats, reserved, bind_error] using
          FrontierRun.exhausted (base := base) (capacity := capacity) (used := used)
            (sorted := true) count reserved
      | some reservation =>
        let fill := fillClaims indices true reservation base capacity indices 0 0 reservation.used
        have countEq : count = retainedClaims indices true indices 0 := by
          simpa only [Nat.zero_add] using countHelpers_count indices indices 0 0 count counted
        have initializedPrefix : FrontierPrefix reservation 0 count fill := by
          rw [countEq]
          exact fillClaims_prefix indices true reservation base capacity indices 0 0 reservation.used
        have certified := FrontierRun.reserved (base := base) (capacity := capacity)
          (used := used) (sorted := true) count reservation fill reserved initializedPrefix
        simp only [helperIndices, validated, counted, bind_unchanged]
        simp only [reserveNats, reserved, bind_success_frame, List.singleton_append]
        simpa only [finishFrontier, frontierOrder, ↓reduceIte] using certified

/-- Successful public output has exactly the reserved number of Nat records.
The outer reservation is the first effect even when that number is zero. -/
theorem FrontierRun.success {base capacity used : Nat} {sorted : Bool}
    {outcome : Outcome NatSlice} (execution : FrontierRun base capacity used sorted outcome)
    (slice : NatSlice) (success : outcome.result = .ok slice) :
    ∃ count, TypedArena.reserve natLayout base capacity used count = some slice.reservation ∧
      slice.values.length = count ∧
      ∃ completed : List FrontierChild, completed.length = count ∧
        slice.values = frontierOrder sorted (completed.map FrontierChild.value) ∧
        outcome.effects = .reserve natLayout count used (some slice.reservation) ::
          (frontierInitializedEffects slice.reservation 0 completed ++
            if sorted then [.sorted slice.reservation.pointer slice.values] else []) := by
  cases execution with
  | refused reason => cases success
  | exhausted count failed => cases success
  | reserved count reservation fill reserved initializedPrefix =>
    cases returned : fill.result with
    | error reason =>
      simp only [finishFrontier, bind, returned] at success
      cases success
    | ok pair =>
      obtain ⟨length, slotEq, completed, completedLength, valuesEq, effects⟩ :=
        initializedPrefix.success pair.1 pair.2 returned
      cases sorted <;>
        simp only [finishFrontier, bind, returned, Bool.false_eq_true, ↓reduceIte,
          unchanged, Except.ok.injEq] at success <;>
        cases success
      · refine ⟨count, reserved, length, completed, completedLength, ?_, ?_⟩
        · simpa only [frontierOrder, Bool.false_eq_true, ↓reduceIte] using valuesEq.symm
        · simp only [finishFrontier, bind, returned, Bool.false_eq_true, ↓reduceIte,
            unchanged, effects, List.append_nil]
      · refine ⟨count, reserved, ?_, completed, completedLength, ?_, ?_⟩
        · simpa only [frontierOrder_length] using length
        · rw [valuesEq]
        · simp only [finishFrontier, bind, returned, ↓reduceIte, effects]

/-- Failure never rolls back the outer array or a completed child. A failed
child is last, its used cursor is returned, and its own slot remains uninitialized.
Sorting is absent from every failure alternative. -/
theorem FrontierRun.failure {base capacity used : Nat} {sorted : Bool}
    {outcome : Outcome NatSlice} (execution : FrontierRun base capacity used sorted outcome)
    (reason : Error) (failed : outcome.result = .error reason) :
    (outcome.used = used ∧ outcome.effects = []) ∨
    (∃ count, TypedArena.reserve natLayout base capacity used count = none ∧
      outcome.used = used ∧ outcome.effects = [.reserve natLayout count used none]) ∨
    (∃ (count : Nat) (reservation : Arena.Reservation)
      (completed : List FrontierChild) (failing : Outcome NatOperand),
      TypedArena.reserve natLayout base capacity used count = some reservation ∧
      completed.length < count ∧ failing.result = .error reason ∧
      outcome.used = failing.used ∧
      outcome.effects = .reserve natLayout count used (some reservation) ::
        (frontierInitializedEffects reservation 0 completed ++ failing.effects)) := by
  cases execution with
  | refused failure => exact Or.inl ⟨rfl, rfl⟩
  | exhausted count reserved => exact Or.inr (Or.inl ⟨count, reserved, rfl, rfl⟩)
  | reserved count reservation fill reserved initializedPrefix =>
    cases returned : fill.result with
    | ok pair =>
      cases sorted <;> simp only [finishFrontier, bind, returned, Bool.false_eq_true,
        ↓reduceIte, unchanged] at failed <;> cases failed
    | error failure =>
      have same : failure = reason := by
        simpa only [finishFrontier, bind, returned, Except.error.injEq] using failed
      subst failure
      obtain ⟨completed, failing, shorter, failure, cursor, effects⟩ := initializedPrefix.failure reason returned
      refine Or.inr (Or.inr ⟨count, reservation, completed, failing, reserved, shorter,
        failure, ?_, ?_⟩)
      · simpa only [finishFrontier, bind, returned] using cursor
      · simpa only [finishFrontier, bind, returned] using congrArg
          (fun effects => Effect.reserve natLayout count used (some reservation) :: effects) effects

/-- Empty collections still execute reserve::<Nat>(0), returning the native
alignment-valued dangling pointer without checking any arena arithmetic. -/
theorem collectPathIndices_nil (base capacity used : Nat) :
    collectPathIndices [] base capacity used =
      ⟨.ok ⟨[], ⟨8, used⟩⟩, used, [.reserve natLayout 0 used (some ⟨8, used⟩)]⟩ := by
  simp only [collectPathIndices, countPaths, bind_unchanged]
  rw [reserveNats_zero]
  rfl

/-- A zero-count successful fill cannot call any initializer. -/
theorem fillLevels_retained_zero (reservation : Arena.Reservation) (keepCandidate : Nat → Bool)
    (make : Nat → Nat → Outcome NatOperand) (remaining level slot used : Nat)
    (zero : retainedLevels keepCandidate remaining level = 0) :
    fillLevels reservation keepCandidate make remaining level slot used = unchanged used (.ok ([], slot)) := by
  induction remaining generalizing level slot used with
  | zero => rfl
  | succ remaining ih =>
    by_cases selected : keepCandidate level = true
    · simp [retainedLevels, selected] at zero
    · have tailZero : retainedLevels keepCandidate remaining (level + 1) = 0 := by
        simpa [retainedLevels, selected] using zero
      simpa [fillLevels, selected] using ih (level + 1) slot used tailZero

theorem fillClaims_retained_zero (indices : List NatOperand) (helpers : Bool)
    (reservation : Arena.Reservation) (base capacity : Nat) (remaining : List NatOperand)
    (claim slot used : Nat) (zero : retainedClaims indices helpers remaining claim = 0) :
    fillClaims indices helpers reservation base capacity remaining claim slot used =
      unchanged used (.ok ([], slot)) := by
  induction remaining generalizing claim slot used with
  | nil => rfl
  | cons index rest ih =>
    have firstZero : retainedLevels (if helpers then isHelper indices index claim else fun _ => true)
        (depth index) 0 = 0 := by simp only [retainedClaims] at zero; omega
    have restZero : retainedClaims indices helpers rest (claim + 1) = 0 := by
      simp only [retainedClaims] at zero; omega
    simp only [fillClaims, fillLevels_retained_zero _ _ _ _ _ _ _ firstZero,
      bind_unchanged, ih (claim + 1) slot used restZero, List.nil_append]

/-- Validated requests with no retained helpers still reserve an empty array and
perform the final in-place sort; no sibling construction or limb allocation occurs. -/
theorem helperIndices_zero (indices : List NatOperand) (base capacity used : Nat)
    (validated : rejectRelated indices = .ok ())
    (counted : countHelpers indices indices 0 0 = .ok 0) :
    helperIndices indices base capacity used =
      ⟨.ok ⟨[], ⟨8, used⟩⟩, used,
        [.reserve natLayout 0 used (some ⟨8, used⟩), .sorted 8 []]⟩ := by
  have zero : retainedClaims indices true indices 0 = 0 := by
    have countEq := countHelpers_count indices indices 0 0 0 counted
    omega
  simp only [helperIndices, validated, counted, bind_unchanged]
  rw [reserveNats_zero]
  simp only [bind_success_frame]
  rw [fillClaims_retained_zero _ _ _ _ _ _ _ _ _ zero]
  simp only [bind_unchanged, List.mergeSort, List.singleton_append]

/-- A nonempty valid request can produce the native empty helper slice. The
closed input checks are kernel reductions; the arena remains completely arbitrary. -/
theorem helperIndices_two_siblings (base capacity used : Nat) :
    helperIndices [.small 2, .small 3] base capacity used =
      ⟨.ok ⟨[], ⟨8, used⟩⟩, used,
        [.reserve natLayout 0 used (some ⟨8, used⟩), .sorted 8 []]⟩ := by
  exact helperIndices_zero [.small 2, .small 3] base capacity used (by rfl) (by rfl)

/-- Every successful public result names precisely its outer typed frame. -/
theorem FrontierRun.success_frame {base capacity used : Nat} {sorted : Bool}
    {outcome : Outcome NatSlice} (execution : FrontierRun base capacity used sorted outcome)
    (slice : NatSlice) (success : outcome.result = .ok slice) :
    TypedArena.reserve natLayout base capacity used slice.values.length = some slice.reservation ∧
      ∃ suffix, outcome.effects =
        .reserve natLayout slice.values.length used (some slice.reservation) :: suffix := by
  obtain ⟨count, reserved, length, completed, _, _, effects⟩ := execution.success slice success
  rw [length]
  exact ⟨reserved, _, effects⟩

/-- Slot writes occupy exactly their 16-byte record inside the committed outer
frame and cannot modify any byte of the caller's previously used prefix. -/
theorem reserved_slot_frame (base capacity used count slot : Nat)
    (reservation : Arena.Reservation)
    (reserved : TypedArena.reserve natLayout base capacity used count = some reservation)
    (inside : slot < count) :
    base + used ≤ reservation.pointer + 16 * slot ∧
      reservation.pointer + 16 * slot + 16 ≤ base + reservation.used ∧
      ∀ address, address < base + used →
        ¬ (reservation.pointer + 16 * slot ≤ address ∧
          address < reservation.pointer + 16 * slot + 16) := by
  rcases reserveNats_frame count base capacity used reservation reserved with
    ⟨zero, _⟩ | ⟨positive, checks, pointer, cursor, ending, monotone⟩
  · omega
  · have lower : base + used ≤ reservation.pointer := by
      rw [pointer]
      unfold TypedArena.start
      omega
    refine ⟨by omega, by omega, ?_⟩
    intro address old overlap
    omega

end SszNative.Indices

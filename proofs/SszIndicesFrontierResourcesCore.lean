import SszIndicesFrontier

set_option autoImplicit false

namespace SszNative.Indices

/-- A count observation only: no candidate values or temporary paths are built. -/
def retainedLevels (keepCandidate : Nat → Bool) : Nat → Nat → Nat
  | 0, _ => 0
  | remaining + 1, level =>
      (if keepCandidate level then 1 else 0) + retainedLevels keepCandidate remaining (level + 1)

def retainedClaims (indices : List NatOperand) (helpers : Bool) : List NatOperand → Nat → Nat
  | [], _ => 0
  | index :: rest, claim =>
      retainedLevels (if helpers then isHelper indices index claim else fun _ => true)
        (depth index) 0 + retainedClaims indices helpers rest (claim + 1)

@[simp] theorem retainedLevels_all (remaining level : Nat) :
    retainedLevels (fun _ => true) remaining level = remaining := by
  induction remaining generalizing level with
  | zero => rfl
  | succ remaining ih => simp [retainedLevels, ih, Nat.add_comm]

theorem countLevels_count (keepCandidate : Nat → Bool) (remaining level count result : Nat)
    (success : countLevels keepCandidate remaining level count = .ok result) :
    result = count + retainedLevels keepCandidate remaining level := by
  induction remaining generalizing level count with
  | zero => simpa [countLevels, retainedLevels] using success.symm
  | succ remaining ih =>
    by_cases selected : keepCandidate level = true
    · by_cases fits : count + 1 < 2^64
      · have next : countLevels keepCandidate remaining (level + 1) (count + 1) = .ok result := by
          simpa [countLevels, selected, fits, Bind.bind, Except.bind] using success
        have counted := ih (level + 1) (count + 1) next
        simpa [retainedLevels, selected, Nat.add_assoc] using counted
      · simp [countLevels, selected, fits, Bind.bind, Except.bind] at success
    · have next : countLevels keepCandidate remaining (level + 1) count = .ok result := by
        simpa [countLevels, selected, Bind.bind, Except.bind] using success
      simpa [retainedLevels, selected] using ih (level + 1) count next

theorem countHelpers_count (indices remaining : List NatOperand) (claim count result : Nat)
    (success : countHelpers indices remaining claim count = .ok result) :
    result = count + retainedClaims indices true remaining claim := by
  induction remaining generalizing claim count with
  | nil => simpa [countHelpers, retainedClaims] using success.symm
  | cons index rest ih =>
    cases counted : countLevels (isHelper indices index claim) (depth index) 0 count with
    | error reason => simp [countHelpers, counted, Bind.bind, Except.bind] at success
    | ok next =>
      have tail : countHelpers indices rest (claim + 1) next = .ok result := by
        simpa [countHelpers, counted, Bind.bind, Except.bind] using success
      have first := countLevels_count _ _ _ _ _ counted
      have second := ih (claim + 1) next tail
      simp only [retainedClaims, ↓reduceIte]
      omega

theorem length_eq_depth_of_success (index : NatOperand) (count : Nat)
    (success : length index = .ok count) : count = depth index := by
  unfold length checkedDepth at success
  split at success
  · simp [Bind.bind, Except.bind] at success
  · by_cases zero : depth index = 0
    · simp [zero, Bind.bind, Except.bind] at success
    · simpa [zero, Bind.bind, Except.bind] using success.symm

theorem countPaths_count (indices remaining : List NatOperand) (claim count result : Nat)
    (success : countPaths remaining count = .ok result) :
    result = count + retainedClaims indices false remaining claim := by
  induction remaining generalizing claim count with
  | nil => simpa [countPaths, retainedClaims] using success.symm
  | cons index rest ih =>
    cases measured : length index with
    | error reason => simp [countPaths, measured, Bind.bind, Except.bind] at success
    | ok amount =>
      by_cases wide : amount ≥ 2^64
      · simp [countPaths, measured, wide, Bind.bind, Except.bind] at success
      · by_cases overflow : count + amount ≥ 2^64
        · simp only [countPaths, measured, wide, overflow, ↓reduceIte, Bind.bind, Except.bind] at success
          cases success
        · have tail : countPaths rest (count + amount) = .ok result := by
            simp only [countPaths, measured, wide, overflow, ↓reduceIte, Bind.bind, Except.bind] at success
            exact success
          have first := length_eq_depth_of_success index amount measured
          have second := ih (claim + 1) (count + amount) tail
          simp only [retainedClaims, Bool.false_eq_true, ↓reduceIte, retainedLevels_all]
          omega

/-- An actual completed child, retaining the entire child outcome. -/
structure FrontierChild where
  call : Outcome NatOperand
  value : NatOperand
  returned : call.result = .ok value

def frontierInitializedEffects (reservation : Arena.Reservation) :
    Nat → List FrontierChild → List Effect
  | _, [] => []
  | slot, child :: rest => child.call.effects ++
      [.initialized reservation.pointer slot child.value] ++
      frontierInitializedEffects reservation (slot + 1) rest

/-- The first failed child has no initialized slot. All previous child effects
and slot initializations are retained, in their original execution order. -/
inductive FrontierPrefix (reservation : Arena.Reservation) :
    Nat → Nat → Outcome (List NatOperand × Nat) → Prop where
  | done (slot used : Nat) :
      FrontierPrefix reservation slot 0 (unchanged used (.ok ([], slot)))
  | failed (slot remaining : Nat) (call : Outcome NatOperand) (reason : Error)
      (returned : call.result = .error reason) :
      FrontierPrefix reservation slot (remaining + 1) ⟨.error reason, call.used, call.effects⟩
  | initialized (slot remaining : Nat) (child : FrontierChild)
      (rest : Outcome (List NatOperand × Nat))
      (suffix : FrontierPrefix reservation (slot + 1) remaining rest) :
      FrontierPrefix reservation slot (remaining + 1)
        ⟨rest.result.map (fun result => (child.value :: result.1, result.2)), rest.used,
          child.call.effects ++ [.initialized reservation.pointer slot child.value] ++ rest.effects⟩

theorem fillLevels_prefix (reservation : Arena.Reservation) (keepCandidate : Nat → Bool)
    (make : Nat → Nat → Outcome NatOperand) (remaining level slot used : Nat) :
    FrontierPrefix reservation slot (retainedLevels keepCandidate remaining level)
      (fillLevels reservation keepCandidate make remaining level slot used) := by
  induction remaining generalizing level slot used with
  | zero => exact .done slot used
  | succ remaining ih =>
    by_cases selected : keepCandidate level = true
    · cases returned : (make level used).result with
      | error reason =>
        simpa only [fillLevels, selected, ↓reduceIte, bind, returned, retainedLevels,
          Nat.add_comm 1] using
          FrontierPrefix.failed (reservation := reservation) slot
            (retainedLevels keepCandidate remaining (level + 1)) (make level used) reason returned
      | ok value =>
        let child : FrontierChild := ⟨make level used, value, returned⟩
        have certified := FrontierPrefix.initialized (reservation := reservation) slot
          (retainedLevels keepCandidate remaining (level + 1)) child
          (fillLevels reservation keepCandidate make remaining (level + 1) (slot + 1) child.call.used)
          (ih (level + 1) (slot + 1) child.call.used)
        cases suffix : (fillLevels reservation keepCandidate make remaining (level + 1)
            (slot + 1) child.call.used).result <;>
          simpa only [fillLevels, selected, ↓reduceIte, bind, returned, suffix, child,
            Except.map, unchanged, retainedLevels, Nat.add_comm 1, List.append_assoc,
            List.cons_append, List.nil_append, List.append_nil] using certified
    · have excluded : keepCandidate level = false := Bool.eq_false_iff.mpr selected
      simpa only [fillLevels, excluded, Bool.false_eq_true, ↓reduceIte, retainedLevels,
        Nat.zero_add] using ih (level + 1) slot used

theorem FrontierPrefix.success {reservation : Arena.Reservation} {slot count : Nat}
    {outcome : Outcome (List NatOperand × Nat)}
    (execution : FrontierPrefix reservation slot count outcome)
    (values : List NatOperand) (finalSlot : Nat)
    (success : outcome.result = .ok (values, finalSlot)) :
    values.length = count ∧ finalSlot = slot + count ∧
      ∃ completed : List FrontierChild, completed.length = count ∧
        completed.map FrontierChild.value = values ∧
        outcome.effects = frontierInitializedEffects reservation slot completed := by
  induction execution generalizing values finalSlot with
  | done slot used =>
    cases success
    exact ⟨rfl, by omega, [], rfl, rfl, rfl⟩
  | failed slot remaining call reason returned => cases success
  | initialized slot remaining child rest suffix ih =>
    cases returned : rest.result with
    | error reason => simp only [returned, Except.map] at success; cases success
    | ok pair =>
      obtain ⟨tail, ending⟩ := pair
      have same : (child.value :: tail, ending) = (values, finalSlot) := by
        simpa only [returned, Except.map, Except.ok.injEq] using success
      have valuesEq : child.value :: tail = values := congrArg Prod.fst same
      have endingEq : ending = finalSlot := congrArg Prod.snd same
      rw [← valuesEq, ← endingEq]
      obtain ⟨length, slotEq, completed, prefixLength, valueEq, effects⟩ := ih tail ending returned
      refine ⟨by simp only [List.length_cons, length], by omega,
        child :: completed, by simp only [List.length_cons, prefixLength], ?_, ?_⟩
      · simp only [List.map_cons, valueEq]
      · simp only [frontierInitializedEffects, effects]

theorem FrontierPrefix.failure {reservation : Arena.Reservation} {slot count : Nat}
    {outcome : Outcome (List NatOperand × Nat)}
    (execution : FrontierPrefix reservation slot count outcome)
    (reason : Error) (failed : outcome.result = .error reason) :
    ∃ completed : List FrontierChild, ∃ failing : Outcome NatOperand,
      completed.length < count ∧ failing.result = .error reason ∧
      outcome.used = failing.used ∧
      outcome.effects = frontierInitializedEffects reservation slot completed ++ failing.effects := by
  induction execution with
  | done slot used => cases failed
  | failed slot remaining call failure returned =>
    cases failed
    exact ⟨[], call, Nat.zero_lt_succ _, returned, rfl, rfl⟩
  | initialized slot remaining child rest suffix ih =>
    cases returned : rest.result with
    | ok pair => simp only [returned, Except.map] at failed; cases failed
    | error failure =>
      have same : failure = reason := by
        simpa only [returned, Except.map, Except.error.injEq] using failed
      subst failure
      obtain ⟨completed, failing, shorter, failedChild, cursor, effects⟩ := ih returned
      refine ⟨child :: completed, failing,
        by simpa only [List.length_cons] using Nat.succ_lt_succ shorter,
        failedChild, cursor, ?_⟩
      simp only [frontierInitializedEffects, effects, List.append_assoc]

/-- Composition is proved for the actual first execution and discharged on the
concrete recursive call below; no public theorem assumes a future run succeeds. -/
theorem FrontierPrefix.append {reservation : Arena.Reservation} {slot count : Nat}
    {first : Outcome (List NatOperand × Nat)}
    (execution : FrontierPrefix reservation slot count first)
    (nextCount : Nat) (next : Nat → Nat → Outcome (List NatOperand × Nat))
    (following : ∀ slot used, FrontierPrefix reservation slot nextCount (next slot used)) :
    FrontierPrefix reservation slot (count + nextCount)
      (bind first fun first cursor => bind (next first.2 cursor) fun second cursor =>
        unchanged cursor (.ok (first.1 ++ second.1, second.2))) := by
  induction execution with
  | done slot used =>
    cases nextEq : next slot used with
    | mk result cursor effects =>
      have certified : FrontierPrefix reservation slot nextCount
          (⟨result, cursor, effects⟩ : Outcome (List NatOperand × Nat)) := by
        simpa only [nextEq] using following slot used
      cases result with
      | error reason =>
        simpa only [bind, unchanged, nextEq, List.nil_append, List.append_nil,
          Nat.zero_add] using certified
      | ok pair =>
        obtain ⟨values, finalSlot⟩ := pair
        simpa only [bind, unchanged, nextEq, List.nil_append, List.append_nil,
          Nat.zero_add] using certified
  | failed slot remaining call reason returned =>
    simpa only [bind, Nat.add_assoc, Nat.add_comm 1 nextCount] using
      FrontierPrefix.failed (reservation := reservation) slot (remaining + nextCount)
        call reason returned
  | initialized slot remaining child rest suffix ih =>
    have certified := FrontierPrefix.initialized (reservation := reservation) slot
      (remaining + nextCount) child
      (bind rest fun first cursor => bind (next first.2 cursor) fun second cursor =>
        unchanged cursor (.ok (first.1 ++ second.1, second.2))) ih
    cases returned : rest.result with
    | error reason =>
      simpa only [bind, returned, Except.map, List.append_assoc, Nat.add_assoc,
        Nat.add_comm 1 nextCount] using certified
    | ok pair =>
      cases nextReturned : (next pair.2 rest.used).result <;>
        simpa only [bind, returned, nextReturned, Except.map, unchanged,
          List.cons_append, List.append_assoc, List.append_nil,
          Nat.add_assoc, Nat.add_comm 1 nextCount] using certified

theorem fillClaims_prefix (indices : List NatOperand) (helpers : Bool)
    (reservation : Arena.Reservation) (base capacity : Nat)
    (remaining : List NatOperand) (claim slot used : Nat) :
    FrontierPrefix reservation slot (retainedClaims indices helpers remaining claim)
      (fillClaims indices helpers reservation base capacity remaining claim slot used) := by
  induction remaining generalizing claim slot used with
  | nil => exact .done slot used
  | cons index rest ih =>
    exact (fillLevels_prefix reservation
      (if helpers then isHelper indices index claim else fun _ => true)
      (if helpers then fun level cursor => shiftXor index level true base capacity cursor
        else fun level cursor => arithmetic cursor (NatShift.shr index level base capacity cursor))
      (depth index) 0 slot used).append
        (retainedClaims indices helpers rest (claim + 1))
        (fun slot used => fillClaims indices helpers reservation base capacity rest
          (claim + 1) slot used)
        (fun slot used => ih (claim + 1) slot used)

end SszNative.Indices

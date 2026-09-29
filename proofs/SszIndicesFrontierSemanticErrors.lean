import SszIndicesFrontierSemanticBuild
import SszNatShiftResources

set_option autoImplicit false

namespace SszNative.Indices

theorem bind_result_error {α β : Type} (first : Outcome α)
    (next : α → Nat → Outcome β) (reason : Error) :
    (bind first next).result = .error reason ↔
      first.result = .error reason ∨
      ∃ value, first.result = .ok value ∧
        (next value first.used).result = .error reason := by
  cases observed : first.result <;> simp [bind, observed]

theorem shiftXor_error (index : NatOperand) (level : Nat) (flip : Bool)
    (base capacity used : Nat) (reason : Error)
    (failed : (shiftXor index level flip base capacity used).result = .error reason) :
    reason = scratch := by
  unfold shiftXor at failed
  cases counted : wordCount (bitLength index - level) with
  | error failure =>
      have same : failure = reason := by simpa [counted, unchanged] using failed
      simpa [same] using wordCount_error _ failure counted
  | ok count =>
      exact makeNat_error _ base capacity used _ reason (by simpa [counted] using failed)

theorem arithmetic_shr_error (index : NatOperand) (level base capacity used : Nat) (reason : Error)
    (failed : (arithmetic used (NatShift.shr index level base capacity used)).result = .error reason) :
    reason = scratch := by
  cases child : (NatShift.shr index level base capacity used).result with
  | ok value => simp [arithmetic, child] at failed
  | error failure =>
      have same : Error.arithmetic failure = reason := by simpa [arithmetic, child] using failed
      have scratchEq := NatShift.shr_error index level base capacity used failure child
      simpa [← same, scratchEq, scratch]

theorem fillLevels_error (reservation : Arena.Reservation) (keepCandidate : Nat → Bool)
    (make : Nat → Nat → Outcome NatOperand)
    (make_error : ∀ level cursor reason, (make level cursor).result = .error reason → reason = scratch)
    (remaining level slot used : Nat) (reason : Error)
    (failed : (fillLevels reservation keepCandidate make remaining level slot used).result = .error reason) :
    reason = scratch := by
  induction remaining generalizing level slot used with
  | zero => simp [fillLevels, unchanged] at failed
  | succ remaining ih =>
      by_cases included : keepCandidate level = true
      · simp only [fillLevels, included, ↓reduceIte] at failed
        rcases (bind_result_error _ _ _).mp failed with child | ⟨value, child, continued⟩
        · exact make_error level used reason child
        · simp only [bind] at continued
          rcases (bind_result_error _ _ _).mp continued with rec | ⟨rest, rec, impossible⟩
          · exact ih (level + 1) (slot + 1) (make level used).used rec
          · simp [unchanged] at impossible
      · have excluded : keepCandidate level = false := Bool.eq_false_iff.mpr included
        exact ih (level + 1) slot used (by simpa [fillLevels, excluded] using failed)

theorem fillClaims_error (indices pending : List NatOperand) (helpers : Bool)
    (reservation : Arena.Reservation) (base capacity claim slot used : Nat) (reason : Error)
    (failed : (fillClaims indices helpers reservation base capacity pending claim slot used).result =
      .error reason) : reason = scratch := by
  induction pending generalizing claim slot used with
  | nil => simp [fillClaims, unchanged] at failed
  | cons index rest ih =>
      unfold fillClaims at failed
      rcases (bind_result_error _ _ _).mp failed with first | ⟨first, filled, continued⟩
      · apply fillLevels_error _ _ _ _ _ _ _ _ reason first
        intro level cursor reason failed
        cases helpers with
        | false => exact arithmetic_shr_error index level base capacity cursor reason failed
        | true => exact shiftXor_error index level true base capacity cursor reason failed
      · rcases (bind_result_error _ _ _).mp continued with rec | ⟨second, rec, impossible⟩
        · exact ih (claim + 1) first.2 _ rec
        · simp [unchanged] at impossible

theorem reserveNats_error (count base capacity used : Nat) (reason : Error)
    (failed : (reserveNats count base capacity used).result = .error reason) : reason = scratch := by
  unfold reserveNats at failed
  split at failed
  · simpa using failed.symm
  · simp at failed

theorem countLevels_error (keepCandidate : Nat → Bool) (remaining level count : Nat) (reason : Error)
    (failed : countLevels keepCandidate remaining level count = .error reason) : reason = scratch := by
  induction remaining generalizing level count with
  | zero => simp [countLevels] at failed
  | succ remaining ih =>
      by_cases included : keepCandidate level = true
      · by_cases room : count + 1 < 2^64
        · exact ih (level + 1) (count + 1)
            (by simpa [countLevels, included, room, Bind.bind, Except.bind] using failed)
        · simpa [countLevels, included, room, Bind.bind, Except.bind] using failed.symm
      · have excluded : keepCandidate level = false := Bool.eq_false_iff.mpr included
        exact ih (level + 1) count
          (by simpa [countLevels, excluded, Bind.bind, Except.bind] using failed)

theorem countHelpers_error (indices pending : List NatOperand) (claim count : Nat) (reason : Error)
    (failed : countHelpers indices pending claim count = .error reason) : reason = scratch := by
  induction pending generalizing claim count with
  | nil => simp [countHelpers] at failed
  | cons index rest ih =>
      cases counted : countLevels (isHelper indices index claim) (depth index) 0 count with
      | error failure =>
          have same : failure = reason := by
            simpa [countHelpers, counted, Bind.bind, Except.bind] using failed
          simpa [same] using countLevels_error _ _ _ _ failure counted
      | ok next =>
          exact ih (claim + 1) next (by simpa [countHelpers, counted, Bind.bind, Except.bind] using failed)

/-- All failures after branch validation are actual scratch exhaustion. -/
theorem branchIndices_error (index : NatOperand) (base capacity used : Nat) (reason : Error)
    (failed : (branchIndices index base capacity used).result = .error reason) :
    length index = .error reason ∨ reason = scratch := by
  unfold branchIndices at failed
  rcases (bind_result_error _ _ _).mp failed with measured | ⟨count, measured, continued⟩
  · exact Or.inl measured
  · right
    simp only [unchanged] at continued
    split at continued
    · simpa [unchanged] using continued.symm
    · rcases (bind_result_error _ _ _).mp continued with reserved | ⟨reservation, reserved, continued⟩
      · exact reserveNats_error count base capacity used reason reserved
      · rcases (bind_result_error _ _ _).mp continued with filled | ⟨result, filled, impossible⟩
        · exact fillLevels_error reservation (fun _ => true)
            (fun level cursor => shiftXor index level true base capacity cursor)
            (fun level cursor reason h => shiftXor_error index level true base capacity cursor reason h)
            count 0 0 _ reason filled
        · simp [unchanged] at impossible

theorem pathIndices_error (index : NatOperand) (base capacity used : Nat) (reason : Error)
    (failed : (pathIndices index base capacity used).result = .error reason) :
    length index = .error reason ∨ reason = scratch := by
  unfold pathIndices at failed
  rcases (bind_result_error _ _ _).mp failed with measured | ⟨count, measured, continued⟩
  · exact Or.inl measured
  · right
    simp only [unchanged] at continued
    split at continued
    · simpa [unchanged] using continued.symm
    · rcases (bind_result_error _ _ _).mp continued with reserved | ⟨reservation, reserved, continued⟩
      · exact reserveNats_error count base capacity used reason reserved
      · rcases (bind_result_error _ _ _).mp continued with filled | ⟨result, filled, impossible⟩
        · exact fillLevels_error reservation (fun _ => true)
            (fun level cursor => arithmetic cursor (NatShift.shr index level base capacity cursor))
            (fun level cursor reason h => arithmetic_shr_error index level base capacity cursor reason h)
            count 0 0 _ reason filled
        · simp [unchanged] at impossible

theorem helperIndices_error (indices : List NatOperand) (base capacity used : Nat) (reason : Error)
    (failed : (helperIndices indices base capacity used).result = .error reason) :
    rejectRelated indices = .error reason ∨ reason = scratch := by
  unfold helperIndices at failed
  rcases (bind_result_error _ _ _).mp failed with accepted | ⟨unit, accepted, continued⟩
  · exact Or.inl accepted
  · right
    rcases (bind_result_error _ _ _).mp continued with counted | ⟨count, counted, continued⟩
    · exact countHelpers_error indices indices 0 0 reason counted
    · rcases (bind_result_error _ _ _).mp continued with reserved | ⟨reservation, reserved, continued⟩
      · exact reserveNats_error count base capacity used reason reserved
      · rcases (bind_result_error _ _ _).mp continued with filled | ⟨result, filled, impossible⟩
        · exact fillClaims_error indices indices true reservation base capacity 0 0 _ reason filled
        · simp at impossible

/-- Total branch refinement distinguishes source validation from actual scratch
failure; it assumes neither a future initializer result nor desired output. -/
theorem branchIndices_refines (index : NatOperand) (base capacity used : Nat)
    (physical : index.words.length < 2^64) :
    eraseResult ((branchIndices index base capacity used).result.map
      (fun result => result.values.map NatOperand.value)) = .ok (Ssz.getBranchIndices index.value) ∨
    (branchIndices index base capacity used).result = .error scratch := by
  cases result : (branchIndices index base capacity used).result with
  | ok values =>
      left
      simp only [Except.map, eraseResult]
      exact congrArg Except.ok (branchIndices_success index base capacity used values physical result).symm
  | error reason =>
      rcases branchIndices_error index base capacity used reason result with measured | exhausted
      · left
        have erased := length_erase index
        rw [measured] at erased
        cases reason <;> simp only [eraseResult, Except.ok.injEq, Except.error_ne_ok] at erased
        all_goals simp [Except.map, eraseResult, Ssz.getBranchIndices, Ssz.getPathIndices,
          ← erased, Bind.bind, Except.bind]
      · simpa [exhausted]

theorem pathIndices_refines (index : NatOperand) (base capacity used : Nat) :
    eraseResult ((pathIndices index base capacity used).result.map
      (fun result => result.values.map NatOperand.value)) = .ok (Ssz.getPathIndices index.value) ∨
    (pathIndices index base capacity used).result = .error scratch := by
  cases result : (pathIndices index base capacity used).result with
  | ok values =>
      left
      simp only [Except.map, eraseResult]
      exact congrArg Except.ok (pathIndices_success index base capacity used values result).symm
  | error reason =>
      rcases pathIndices_error index base capacity used reason result with measured | exhausted
      · left
        have erased := length_erase index
        rw [measured] at erased
        cases reason <;> simp only [eraseResult, Except.ok.injEq, Except.error_ne_ok] at erased
        all_goals simp [Except.map, eraseResult, Ssz.getPathIndices, ← erased, Bind.bind, Except.bind]
      · simpa [exhausted]

theorem helperIndices_refines (indices : List NatOperand) (base capacity used : Nat)
    (physical : ∀ index ∈ indices, index.words.length < 2^64) :
    eraseResult ((helperIndices indices base capacity used).result.map
      (fun result => result.values.map NatOperand.value)) =
      .ok (Ssz.getHelperIndices (indices.map NatOperand.value)) ∨
    (helperIndices indices base capacity used).result = .error scratch := by
  cases result : (helperIndices indices base capacity used).result with
  | ok values =>
      left
      simp only [Except.map, eraseResult]
      exact congrArg Except.ok (helperIndices_success indices base capacity used values physical result).symm
  | error reason =>
      rcases helperIndices_error indices base capacity used reason result with accepted | exhausted
      · left
        have erased := rejectRelated_erase indices physical
        rw [accepted] at erased
        cases reason <;> simp only [eraseResult, Except.ok.injEq, Except.error_ne_ok] at erased
        all_goals simp [Except.map, eraseResult, Ssz.getHelperIndices, ← erased, Bind.bind, Except.bind]
      · simpa [exhausted]

/-- A count overflow can precede a later semantic refusal; only actual
overflow may select the scratch branch of this total preflight relation. -/
theorem countPaths_error (indices : List NatOperand) (count : Nat) (reason : Error)
    (failed : countPaths indices count = .error reason) :
    eraseResult (.error reason : Except Error (List Nat)) =
      .ok (Ssz.collectPathIndices (indices.map NatOperand.value)) ∨ reason = scratch := by
  induction indices generalizing count with
  | nil => simp [countPaths] at failed
  | cons index rest ih =>
      cases measured : length index with
      | error failure =>
          have same : failure = reason := by
            simpa [countPaths, measured, Bind.bind, Except.bind] using failed
          subst failure
          left
          have erased := length_erase index
          rw [measured] at erased
          cases reason <;> simp only [eraseResult, Except.ok.injEq, Except.error_ne_ok] at erased
          all_goals
            simp [eraseResult, Ssz.collectPathIndices, Ssz.getPathIndices,
              ← erased, Bind.bind, Except.bind]
      | ok amount =>
          by_cases wide : amount ≥ 2^64
          · right
            simpa [countPaths, measured, wide, Bind.bind, Except.bind] using failed.symm
          · by_cases overflow : count + amount ≥ 2^64
            · right
              simpa [countPaths, measured, wide, overflow, Bind.bind, Except.bind] using failed.symm
            · have rec : countPaths rest (count + amount) = .error reason := by
                simpa [countPaths, measured, wide, overflow, Bind.bind, Except.bind] using failed
              rcases ih (count + amount) rec with semantic | exhausted
              · left
                have erased := length_erase index
                rw [measured] at erased
                have pinned : Ssz.gindexLength index.value = .ok amount := by
                  simpa [eraseResult] using erased.symm
                cases reason <;>
                  simp only [eraseResult, Except.ok.injEq, Except.error_ne_ok] at semantic
                all_goals
                  simp [eraseResult, Ssz.collectPathIndices, Ssz.getPathIndices,
                    pinned, ← semantic, Bind.bind, Except.bind]
              · exact Or.inr exhausted

theorem collectPathIndices_error (indices : List NatOperand) (base capacity used : Nat)
    (reason : Error)
    (failed : (collectPathIndices indices base capacity used).result = .error reason) :
    countPaths indices 0 = .error reason ∨ reason = scratch := by
  unfold collectPathIndices at failed
  rcases (bind_result_error _ _ _).mp failed with counted | ⟨count, counted, continued⟩
  · exact Or.inl counted
  · right
    rcases (bind_result_error _ _ _).mp continued with reserved | ⟨reservation, reserved, continued⟩
    · exact reserveNats_error count base capacity used reason reserved
    · rcases (bind_result_error _ _ _).mp continued with filled | ⟨result, filled, impossible⟩
      · exact fillClaims_error indices indices false reservation base capacity 0 0 _ reason filled
      · simp [unchanged] at impossible

theorem collectPathIndices_refines (indices : List NatOperand) (base capacity used : Nat) :
    eraseResult ((collectPathIndices indices base capacity used).result.map
      (fun result => result.values.map NatOperand.value)) =
      .ok (Ssz.collectPathIndices (indices.map NatOperand.value)) ∨
    (collectPathIndices indices base capacity used).result = .error scratch := by
  cases result : (collectPathIndices indices base capacity used).result with
  | ok values =>
      left
      simp only [Except.map, eraseResult]
      exact congrArg Except.ok (collectPathIndices_success indices base capacity used values result).symm
  | error reason =>
      rcases collectPathIndices_error indices base capacity used reason result with counted | exhausted
      · rcases countPaths_error indices 0 reason counted with semantic | exhausted
        · exact Or.inl semantic
        · simpa [exhausted]
      · simpa [exhausted]

end SszNative.Indices

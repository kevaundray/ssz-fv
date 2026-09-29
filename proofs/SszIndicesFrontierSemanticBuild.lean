import SszIndicesFrontierSemanticValidation
import SszIndicesFrontierOrder
import SszIndicesFrontierCandidates
import SszIndicesArithmeticPhysical
import SszIndicesFrontierMembershipComplete
import SszIndicesFrontierUnique

set_option autoImplicit false

namespace SszNative.Indices

theorem candidateLevels_filter (keepCandidate : Nat → Bool) (remaining level : Nat) :
    candidateLevels keepCandidate remaining level = (List.range' level remaining).filter keepCandidate := by
  induction remaining generalizing level with
  | zero => rfl
  | succ remaining ih =>
      by_cases included : keepCandidate level = true <;>
        simp [candidateLevels, List.range'_succ, included, ih]

/-- The branch initializes only the reserved slots, in leaf-up source order. -/
theorem branchIndices_success (index : NatOperand) (base capacity used : Nat) (result : NatSlice)
    (physical : index.words.length < 2^64)
    (success : (branchIndices index base capacity used).result = .ok result) :
    Ssz.getBranchIndices index.value = .ok (result.values.map NatOperand.value) := by
  unfold branchIndices at success
  obtain ⟨count, measured, continued⟩ := (bind_result_ok _ _ _).mp success
  have measured' : length index = .ok count := measured
  simp only [unchanged] at continued
  split at continued
  · simp [unchanged] at continued
  · obtain ⟨reservation, reserved, continued⟩ := (bind_result_ok _ _ _).mp continued
    obtain ⟨filled, filledEq, returned⟩ := (bind_result_ok _ _ _).mp continued
    have same : (⟨filled.1, reservation⟩ : NatSlice) = result := by
      simpa [unchanged] using returned
    cases same
    obtain ⟨values, slots⟩ := fillLevels_success reservation (fun _ => true)
      (fun level cursor => shiftXor index level true base capacity cursor)
      (fun level => Ssz.gindexSibling (index.value >>> level))
      (fun level cursor value h => shiftXor_value index level true base capacity cursor value physical h)
      count 0 0 (reserveNats count base capacity used).used filled.1 filled.2 filledEq
    have erased := length_erase index
    rw [measured'] at erased
    have pinned : Ssz.gindexLength index.value = .ok count := by
      simpa [eraseResult] using erased.symm
    rw [candidateLevels_true] at values
    simpa [Ssz.getBranchIndices, Ssz.getPathIndices, pinned, Bind.bind, Except.bind,
      List.map_map, List.range_eq_range'] using congrArg (Except.ok (ε := Ssz.Err)) values.symm

/-- Generic pointwise closure uses only children that were actually completed. -/
theorem fillLevels_all (reservation : Arena.Reservation) (keepCandidate : Nat → Bool)
    (make : Nat → Nat → Outcome NatOperand) (property : NatOperand → Prop)
    (make_property : ∀ level cursor value, (make level cursor).result = .ok value → property value)
    (remaining level slot used : Nat) (values : List NatOperand) (nextSlot : Nat)
    (success : (fillLevels reservation keepCandidate make remaining level slot used).result =
      .ok (values, nextSlot)) : ∀ value ∈ values, property value := by
  induction remaining generalizing level slot used values nextSlot with
  | zero =>
      have same : ([], slot) = (values, nextSlot) := by simpa [fillLevels, unchanged] using success
      cases same
      simp
  | succ remaining ih =>
      by_cases included : keepCandidate level = true
      · simp only [fillLevels, included, ↓reduceIte] at success
        obtain ⟨value, made, continued⟩ := (bind_result_ok _ _ _).mp success
        simp only [bind] at continued
        obtain ⟨rest, filled, returned⟩ := (bind_result_ok _ _ _).mp continued
        have same : (value :: rest.1, rest.2) = (values, nextSlot) := by
          simpa [unchanged] using returned
        cases same
        have restProperty := ih (level + 1) (slot + 1) (make level used).used rest.1 rest.2 filled
        intro selected member
        rcases List.mem_cons.mp member with equal | member
        · simpa [equal] using make_property level used value made
        · exact restProperty selected member
      · have excluded : keepCandidate level = false := Bool.eq_false_iff.mpr included
        exact ih (level + 1) slot used values nextSlot
          (by simpa [fillLevels, excluded] using success)

theorem branchIndices_success_physical (index : NatOperand) (base capacity used : Nat)
    (result : NatSlice) (success : (branchIndices index base capacity used).result = .ok result) :
    ∀ value ∈ result.values, value.words.length < 2^64 := by
  unfold branchIndices at success
  obtain ⟨count, measured, continued⟩ := (bind_result_ok _ _ _).mp success
  simp only [unchanged] at continued
  split at continued
  · simp [unchanged] at continued
  · obtain ⟨reservation, reserved, continued⟩ := (bind_result_ok _ _ _).mp continued
    obtain ⟨filled, filledEq, returned⟩ := (bind_result_ok _ _ _).mp continued
    have same : (⟨filled.1, reservation⟩ : NatSlice) = result := by simpa [unchanged] using returned
    cases same
    exact fillLevels_all reservation (fun _ => true)
      (fun level cursor => shiftXor index level true base capacity cursor)
      (fun value => value.words.length < 2^64)
      (fun level cursor value h => shiftXor_success_physical index level true base capacity cursor value h)
      count 0 0 _ filled.1 filled.2 filledEq

theorem fillClaims_helpers_values (indices pending : List NatOperand)
    (reservation : Arena.Reservation) (base capacity claim slot used : Nat)
    (physical : ∀ index ∈ pending, index.words.length < 2^64)
    (values : List NatOperand) (nextSlot : Nat)
    (success : (fillClaims indices true reservation base capacity pending claim slot used).result =
      .ok (values, nextSlot)) :
    values.map NatOperand.value = (pending.zipIdx claim).flatMap (fun pair =>
      ((List.range (depth pair.1)).filter (isHelper indices pair.1 pair.2)).map
        (fun level => Ssz.gindexSibling (pair.1.value >>> level))) := by
  induction pending generalizing claim slot used values nextSlot with
  | nil =>
      have same : ([], slot) = (values, nextSlot) := by simpa [fillClaims, unchanged] using success
      cases same
      rfl
  | cons index rest ih =>
      simp only [fillClaims, Bool.true_eq, ↓reduceIte] at success
      obtain ⟨first, firstEq, continued⟩ := (bind_result_ok _ _ _).mp success
      obtain ⟨second, secondEq, returned⟩ := (bind_result_ok _ _ _).mp continued
      have same : (first.1 ++ second.1, second.2) = (values, nextSlot) := by
        simpa [unchanged] using returned
      cases same
      have firstValues := (fillLevels_success reservation (isHelper indices index claim)
        (fun level cursor => shiftXor index level true base capacity cursor)
        (fun level => Ssz.gindexSibling (index.value >>> level))
        (fun level cursor value h => shiftXor_value index level true base capacity cursor value
          (physical index (by simp)) h)
        (depth index) 0 slot used first.1 first.2 firstEq).1
      have restValues := ih (claim + 1) first.2 _
        (fun value member => physical value (by simp [member])) second.1 second.2 secondEq
      simp [List.map_append, firstValues, restValues, candidateLevels_filter, List.range_eq_range']

theorem fillClaims_helpers_physical (indices pending : List NatOperand)
    (reservation : Arena.Reservation) (base capacity claim slot used : Nat)
    (values : List NatOperand) (nextSlot : Nat)
    (success : (fillClaims indices true reservation base capacity pending claim slot used).result =
      .ok (values, nextSlot)) : ∀ value ∈ values, value.words.length < 2^64 := by
  induction pending generalizing claim slot used values nextSlot with
  | nil =>
      have same : ([], slot) = (values, nextSlot) := by simpa [fillClaims, unchanged] using success
      cases same
      simp
  | cons index rest ih =>
      simp only [fillClaims, Bool.true_eq, ↓reduceIte] at success
      obtain ⟨first, firstEq, continued⟩ := (bind_result_ok _ _ _).mp success
      obtain ⟨second, secondEq, returned⟩ := (bind_result_ok _ _ _).mp continued
      have same : (first.1 ++ second.1, second.2) = (values, nextSlot) := by
        simpa [unchanged] using returned
      cases same
      have firstPhysical := fillLevels_all reservation (isHelper indices index claim)
        (fun level cursor => shiftXor index level true base capacity cursor)
        (fun value => value.words.length < 2^64)
        (fun level cursor value h => shiftXor_success_physical index level true base capacity cursor value h)
        (depth index) 0 slot used first.1 first.2 firstEq
      have restPhysical := ih (claim + 1) first.2 _ second.1 second.2 secondEq
      intro value member
      rcases List.mem_append.mp member with firstMember | secondMember
      · exact firstPhysical value firstMember
      · exact restPhysical value secondMember

theorem helperIndices_success_physical (indices : List NatOperand) (base capacity used : Nat)
    (result : NatSlice) (success : (helperIndices indices base capacity used).result = .ok result) :
    ∀ value ∈ result.values, value.words.length < 2^64 := by
  unfold helperIndices at success
  obtain ⟨unit, accepted, continued⟩ := (bind_result_ok _ _ _).mp success
  obtain ⟨count, counted, continued⟩ := (bind_result_ok _ _ _).mp continued
  obtain ⟨reservation, reserved, continued⟩ := (bind_result_ok _ _ _).mp continued
  obtain ⟨filled, filledEq, returned⟩ := (bind_result_ok _ _ _).mp continued
  have same : (⟨filled.1.mergeSort (fun left right => right.value ≤ left.value), reservation⟩ : NatSlice) =
      result := by simpa using returned
  cases same
  intro value member
  exact fillClaims_helpers_physical indices indices reservation base capacity 0 0 _
    filled.1 filled.2 filledEq value (List.mem_mergeSort.mp member)

theorem pinned_collect_of_valid (indices : List Nat) (valid : ∀ index ∈ indices, 2 ≤ index) :
    Ssz.collectPathIndices indices = .ok (claimPaths indices) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      have named := valid index (by simp)
      have positive : 1 ≤ index.log2 :=
        (Nat.le_log2 (by omega)).mpr (by simpa using named)
      have measured : Ssz.gindexLength index = .ok index.log2 := by
        simp [Ssz.gindexLength, Ssz.gindexDepth, show ¬ index < 1 by omega,
          show index.log2 ≠ 0 by omega, Bind.bind, Except.bind]
      have restValid := ih (fun value member => valid value (by simp [member]))
      simp [Ssz.collectPathIndices, Ssz.getPathIndices, measured, restValid, claimPaths,
        Bind.bind, Except.bind]

/-- Retained-only fill followed by descending numeric sort equals the pinned
deduplicated sibling union minus paths; the premise is actual resource success. -/
theorem helperIndices_success (indices : List NatOperand) (base capacity used : Nat)
    (result : NatSlice) (physical : ∀ index ∈ indices, index.words.length < 2^64)
    (success : (helperIndices indices base capacity used).result = .ok result) :
    Ssz.getHelperIndices (indices.map NatOperand.value) = .ok (result.values.map NatOperand.value) := by
  unfold helperIndices at success
  obtain ⟨unit, accepted, continued⟩ := (bind_result_ok _ _ _).mp success
  cases unit
  have accepted' : rejectRelated indices = .ok () := accepted
  obtain ⟨count, counted, continued⟩ := (bind_result_ok _ _ _).mp continued
  obtain ⟨reservation, reserved, continued⟩ := (bind_result_ok _ _ _).mp continued
  obtain ⟨filled, filledEq, returned⟩ := (bind_result_ok _ _ _).mp continued
  have same : (⟨filled.1.mergeSort (fun left right => right.value ≤ left.value), reservation⟩ : NatSlice) =
      result := by simpa using returned
  cases same
  have values := fillClaims_helpers_values indices indices reservation base capacity 0 0 _
    physical filled.1 filled.2 filledEq
  have candidates : filled.1.map NatOperand.value = helperCandidates indices := by
    simpa [helperCandidates, helperCandidateKeys, List.map_flatMap, List.map_map,
      helperCandidateValue] using values
  have valid := rejectRelated_valid indices accepted'
  have erased := rejectRelated_erase indices physical
  rw [accepted'] at erased
  have pinnedAccepted : Ssz.rejectRelated (indices.map NatOperand.value) = .ok () := by
    simpa [eraseResult] using erased.symm
  have mappedValid : ∀ index ∈ indices.map NatOperand.value, 2 ≤ index := by
    intro value member
    obtain ⟨index, member, same⟩ := List.mem_map.mp member
    simpa [same] using valid index member
  have collected := pinned_collect_of_valid (indices.map NatOperand.value) mappedValid
  let paths := claimPaths (indices.map NatOperand.value)
  let expected := ((paths.map Ssz.gindexSibling).eraseDups.filter
    (fun node => !paths.contains node)).mergeSort (fun a b => b ≤ a)
  have pinned : Ssz.getHelperIndices (indices.map NatOperand.value) = .ok expected := by
    simp [Ssz.getHelperIndices, pinnedAccepted, collected, expected, paths, Bind.bind, Except.bind]
  have ordered := sorted_frontier_eq (indices.map NatOperand.value) expected (helperCandidates indices)
    pinned (helperCandidates_nodup indices physical valid)
    (helperCandidates_membership indices physical valid)
  rw [values_mergeSort, candidates, ordered]
  exact pinned

end SszNative.Indices

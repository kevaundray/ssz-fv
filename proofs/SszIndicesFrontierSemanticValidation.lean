import SszIndicesFrontierSemanticCore
import SszIndicesFrontierSemanticPaths

set_option autoImplicit false

namespace SszNative.Indices

@[simp] theorem sameValue_eq (left right : NatOperand) :
    sameValue left right = (left.value == right.value) := by
  apply Bool.eq_iff_iff.mpr
  simp only [sameValue, beq_iff_eq, Limbs.nativeCmp_correct, Nat.compare_eq_eq]
  rfl

@[simp] theorem sameValue_any (indices : List NatOperand) (index : NatOperand) :
    indices.any (sameValue index) = (indices.map NatOperand.value).contains index.value := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, sameValue_eq, beq_iff_eq, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨value, member, same⟩
    exact ⟨value, member, same.symm⟩
  · rintro ⟨value, member, same⟩
    exact ⟨value, member, same.symm⟩

/-- The different ancestor scan orders have the same claim-only refusal payload. -/
theorem pinned_rejectAncestors_any (indices : List Nat) (claim : Nat) (ancestors : List Nat) :
    Ssz.rejectAncestors indices claim ancestors =
      if ancestors.any indices.contains then .error (.nestedIndex claim) else .ok () := by
  induction ancestors with
  | nil => rfl
  | cons ancestor rest ih =>
      simp only [Ssz.rejectAncestors, List.any_cons]
      rcases Bool.eq_false_or_eq_true (indices.contains ancestor) with present | absent
      · simp only [present, ↓reduceIte]
        rfl
      · simp only [absent, Bool.false_eq_true, ↓reduceIte]
        exact ih

/-- Literal ancestor rejection needs no validity or physical-storage premise. -/
theorem rejectAncestors_erase (indices : List NatOperand) (claim : NatOperand)
    (ancestors : List NatOperand) :
    eraseResult (rejectAncestors indices claim ancestors) =
      .ok (Ssz.rejectAncestors (indices.map NatOperand.value) claim.value
        (ancestors.map NatOperand.value)) := by
  rw [pinned_rejectAncestors_any]
  simp only [rejectAncestors, sameValue_any, List.any_map, Function.comp_def]
  split <;> simp only [eraseResult]

private theorem bool_or_false (left right : Bool) :
    (left || right) = false ↔ left = false ∧ right = false := by
  cases left <;> cases right <;> decide

/-- A repeated claim is detected by value even when the raw representations differ. -/
theorem repeated_false_iff (earlier pending : List NatOperand) :
    repeated earlier pending = false ↔
      (pending.map NatOperand.value).Nodup ∧
      ∀ index ∈ pending, index.value ∉ earlier.map NatOperand.value := by
  induction pending generalizing earlier with
  | nil => simp [repeated]
  | cons index rest ih =>
      rw [repeated, bool_or_false, sameValue_any, ih]
      simp only [Bool.eq_false_iff]
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · rintro ⟨absent, unique, disjoint⟩
        refine ⟨⟨?_, unique⟩, ?_⟩
        · intro member
          obtain ⟨other, member, equal⟩ := List.mem_map.mp member
          exact disjoint other member (by simp [equal])
        · intro other member
          rcases List.mem_cons.mp member with equal | member
          · simpa [equal] using absent
          · intro present
            exact disjoint other member (by simp [present])
      · rintro ⟨⟨absent, unique⟩, disjoint⟩
        refine ⟨(fun present => disjoint index (by simp) (List.contains_iff_mem.mp present)),
          unique, ?_⟩
        intro other member present
        rcases List.mem_cons.mp present with equal | present
        · exact absent (List.mem_map.mpr ⟨other, member, equal⟩)
        · exact disjoint other (by simp [member]) present

private theorem dedup_info (indices : List Nat) :
    List.Sublist indices.eraseDups indices ∧ indices.eraseDups.Nodup := by
  cases indices with
  | nil => simp
  | cons head rest =>
      rw [List.eraseDups_cons]
      have filtered := dedup_info (rest.filter fun item => !item == head)
      constructor
      · exact List.Sublist.cons_cons _ (filtered.1.trans List.filter_sublist)
      · rw [List.nodup_cons]
        exact ⟨by simp, filtered.2⟩
termination_by indices.length
decreasing_by have := List.length_filter_le (fun item => !item == head) rest; simp_all; omega

private theorem dedup_eq_self (indices : List Nat) (unique : indices.Nodup) :
    indices.eraseDups = indices := by
  induction indices with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      have filtered : rest.filter (fun item => !item == head) = rest := by
        apply List.filter_eq_self.mpr
        intro item member
        have different : item ≠ head := by intro equal; subst item; exact absent member
        simp [different]
      rw [List.eraseDups_cons, filtered, ih tailUnique]

theorem dedup_length_iff (indices : List Nat) :
    indices.eraseDups.length = indices.length ↔ indices.Nodup := by
  constructor
  · intro lengths
    have same := (dedup_info indices).1.eq_of_length lengths
    rw [← same]
    exact (dedup_info indices).2
  · intro unique
    rw [dedup_eq_self indices unique]

/-- The whole duplicate pass precedes every zero/root/ancestor check. -/
theorem repeated_eq_pinned (indices : List NatOperand) :
    repeated [] indices =
      ((indices.map NatOperand.value).eraseDups.length != (indices.map NatOperand.value).length) := by
  have same : repeated [] indices = false ↔ (indices.map NatOperand.value).Nodup := by
    simpa using repeated_false_iff [] indices
  cases observed : repeated [] indices with
  | false =>
      have lengths := (dedup_length_iff (indices.map NatOperand.value)).mpr (same.mp observed)
      simp only [lengths, bne_self_eq_false]
  | true =>
      have unequal : (indices.map NatOperand.value).eraseDups.length ≠
          (indices.map NatOperand.value).length := by
        intro equal
        have absent := same.mpr ((dedup_length_iff _).mp equal)
        rw [observed] at absent
        cases absent
      symm
      exact (bne_iff_ne).mpr unequal

theorem ancestor_scan_eq (indices : List NatOperand) (claim : NatOperand) (count : Nat)
    (measured : length claim = .ok count)
    (physical : ∀ index ∈ indices, index.words.length < 2^64)
    (claimPhysical : claim.words.length < 2^64) :
    indices.any (fun ancestor =>
      depth ancestor != 0 && depth ancestor < count &&
        prefixEqual claim (count - depth ancestor) false ancestor 0) =
    (((List.range count).map (fun level => claim.value >>> level)).drop 1).any
      (indices.map NatOperand.value).contains := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨ancestor, member, compared⟩
    exact ⟨ancestor.value, (ancestor_test_iff claim ancestor count measured claimPhysical
      (physical ancestor member)).mp compared, List.mem_map.mpr ⟨ancestor, member, rfl⟩⟩
  · rintro ⟨value, ancestor, member⟩
    obtain ⟨index, indexMember, same⟩ := List.mem_map.mp member
    subst value
    exact ⟨index, indexMember, (ancestor_test_iff claim index count measured claimPhysical
      (physical index indexMember)).mpr ancestor⟩

/-- Borrowed validation preserves request-order refusal, including zero and root. -/
theorem rejectClaimPaths_erase (indices pending : List NatOperand)
    (physical : ∀ index ∈ indices, index.words.length < 2^64)
    (pendingPhysical : ∀ index ∈ pending, index.words.length < 2^64) :
    eraseResult (rejectClaimPaths indices pending) =
      .ok (Ssz.rejectClaimPaths (indices.map NatOperand.value) (pending.map NatOperand.value)) := by
  induction pending with
  | nil => rfl
  | cons claim rest ih =>
      have tailPhysical : ∀ index ∈ rest, index.words.length < 2^64 :=
        fun index member => pendingPhysical index (by simp [member])
      have tail := ih tailPhysical
      have erased := length_erase claim
      cases measured : length claim with
      | error reason =>
          rw [measured] at erased
          cases reason <;>
            simp only [eraseResult, Except.ok.injEq, reduceCtorEq] at erased
          all_goals
            simp [rejectClaimPaths, measured, Ssz.rejectClaimPaths, Ssz.getPathIndices,
              ← erased, eraseResult, Bind.bind, Except.bind]
      | ok count =>
          rw [measured] at erased
          have pinned : Ssz.gindexLength claim.value = .ok count := by
            simpa [eraseResult] using erased.symm
          have scan := ancestor_scan_eq indices claim count measured physical
            (pendingPhysical claim (by simp))
          simp only [rejectClaimPaths, measured, Bind.bind, Except.bind]
          rw [scan]
          simp only [List.map_cons, Ssz.rejectClaimPaths, Ssz.getPathIndices, pinned,
            Bind.bind, Except.bind, Pure.pure, Except.pure, pinned_rejectAncestors_any]
          cases detected : (((List.range count).map (fun level => claim.value >>> level)).drop 1).any
              (indices.map NatOperand.value).contains with
          | false => exact tail
          | true => rfl

/-- Empty and duplicate passes finish before request-ordered path validation. -/
theorem rejectRelated_erase (indices : List NatOperand)
    (physical : ∀ index ∈ indices, index.words.length < 2^64) :
    eraseResult (rejectRelated indices) =
      .ok (Ssz.rejectRelated (indices.map NatOperand.value)) := by
  have paths := rejectClaimPaths_erase indices indices physical physical
  have repeatedEq := repeated_eq_pinned indices
  cases indices with
  | nil => rfl
  | cons index rest =>
      unfold rejectRelated Ssz.rejectRelated
      rw [← repeatedEq]
      cases repeats : repeated [] (index :: rest) with
      | false => exact paths
      | true => rfl

theorem rejectClaimPaths_valid (indices pending : List NatOperand)
    (accepted : rejectClaimPaths indices pending = .ok ()) :
    ∀ index ∈ pending, 2 ≤ index.value := by
  induction pending with
  | nil => simp
  | cons claim rest ih =>
      cases measured : length claim with
      | error reason => simp [rejectClaimPaths, measured, Bind.bind, Except.bind] at accepted
      | ok count =>
          simp only [rejectClaimPaths, measured, Bind.bind, Except.bind] at accepted
          split at accepted
          · cases accepted
          · have restValid := ih accepted
            intro index member
            rcases List.mem_cons.mp member with same | member
            · simpa [same] using (length_success claim count measured).2.2
            · exact restValid index member

theorem rejectRelated_valid (indices : List NatOperand)
    (accepted : rejectRelated indices = .ok ()) :
    ∀ index ∈ indices, 2 ≤ index.value := by
  have paths : rejectClaimPaths indices indices = .ok () := by
    unfold rejectRelated at accepted
    cases empty : indices.isEmpty with
    | true =>
        rw [empty] at accepted
        cases accepted
    | false =>
        rw [empty] at accepted
        cases repeats : repeated [] indices with
        | false =>
            rw [repeats] at accepted
            exact accepted
        | true =>
            rw [repeats] at accepted
            cases accepted
  exact rejectClaimPaths_valid indices indices paths

end SszNative.Indices

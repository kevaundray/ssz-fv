import SszIndicesFrontier
import SszNatShiftSemantics
import SszIndicesPinnedFrontier
import SszIndicesFrontierResourcesCore

set_option autoImplicit false

namespace SszNative.Indices

/-- Successful composition exposes the actual child result and retained cursor. -/
theorem bind_result_ok {α β : Type} (first : Outcome α)
    (next : α → Nat → Outcome β) (result : β) :
    (bind first next).result = .ok result ↔
      ∃ value, first.result = .ok value ∧
        (next value first.used).result = .ok result := by
  cases observed : first.result <;> simp [bind, observed]

/-- Observational enumeration only; the native count pass does not allocate it. -/
def candidateLevels (keepCandidate : Nat → Bool) : Nat → Nat → List Nat
  | 0, _ => []
  | remaining + 1, level =>
      if keepCandidate level then level :: candidateLevels keepCandidate remaining (level + 1)
      else candidateLevels keepCandidate remaining (level + 1)

theorem candidateLevels_true (remaining level : Nat) :
    candidateLevels (fun _ => true) remaining level = List.range' level remaining := by
  induction remaining generalizing level with
  | zero => simp [candidateLevels]
  | succ remaining ih => simp [candidateLevels, List.range'_succ, ih]

/-- The checked first pass counts exactly the candidates that the second pass visits. -/
theorem countLevels_success (keepCandidate : Nat → Bool) (remaining level count result : Nat)
    (success : countLevels keepCandidate remaining level count = .ok result) :
    result = count + (candidateLevels keepCandidate remaining level).length := by
  induction remaining generalizing level count result with
  | zero => simpa [countLevels, candidateLevels] using success.symm
  | succ remaining ih =>
      by_cases included : keepCandidate level = true
      · by_cases room : count + 1 < 2^64
        · have recursive : countLevels keepCandidate remaining (level + 1) (count + 1) = .ok result := by
            simpa [countLevels, included, room, Bind.bind, Except.bind] using success
          have measured := ih (level + 1) (count + 1) result recursive
          simp only [candidateLevels, included, ↓reduceIte, List.length_cons]
          omega
        · simp [countLevels, included, room, Bind.bind, Except.bind] at success
      · have excluded : keepCandidate level = false := Bool.eq_false_iff.mpr included
        have recursive : countLevels keepCandidate remaining (level + 1) count = .ok result := by
          simpa [countLevels, excluded, Bind.bind, Except.bind] using success
        simpa [candidateLevels, excluded] using ih (level + 1) count result recursive

/-- A successful fill has precisely the selected values, in ascending loop order,
with one initialized slot for each selected candidate. Arithmetic correctness is
used only for a child which actually returned successfully. -/
theorem fillLevels_success (reservation : Arena.Reservation) (keepCandidate : Nat → Bool)
    (make : Nat → Nat → Outcome NatOperand) (observe : Nat → Nat)
    (make_value : ∀ level cursor value, (make level cursor).result = .ok value →
      value.value = observe level)
    (remaining level slot used : Nat) (values : List NatOperand) (nextSlot : Nat)
    (success : (fillLevels reservation keepCandidate make remaining level slot used).result =
      .ok (values, nextSlot)) :
    values.map NatOperand.value = (candidateLevels keepCandidate remaining level).map observe ∧
      nextSlot = slot + (candidateLevels keepCandidate remaining level).length := by
  induction remaining generalizing level slot used values nextSlot with
  | zero =>
      have same : ([], slot) = (values, nextSlot) := by
        simpa [fillLevels, unchanged] using success
      cases same
      simp [candidateLevels]
  | succ remaining ih =>
      by_cases included : keepCandidate level = true
      · simp only [fillLevels, included, ↓reduceIte] at success
        obtain ⟨value, made, continued⟩ := (bind_result_ok _ _ _).mp success
        change (bind (fillLevels reservation keepCandidate make remaining (level + 1)
          (slot + 1) (make level used).used)
          (fun rest cursor => unchanged cursor (.ok (value :: rest.1, rest.2)))).result =
          .ok (values, nextSlot) at continued
        obtain ⟨rest, filled, returned⟩ := (bind_result_ok _ _ _).mp continued
        have same : (value :: rest.1, rest.2) = (values, nextSlot) := by
          simpa [unchanged] using returned
        cases same
        obtain ⟨mapped, slots⟩ := ih (level + 1) (slot + 1) (make level used).used
          rest.1 rest.2 filled
        constructor
        · simp [candidateLevels, included, make_value level used value made, mapped]
        · simp only [candidateLevels, included, ↓reduceIte, List.length_cons]
          omega
      · have excluded : keepCandidate level = false := Bool.eq_false_iff.mpr included
        have recursive : (fillLevels reservation keepCandidate make remaining (level + 1) slot used).result =
            .ok (values, nextSlot) := by
          simpa [fillLevels, excluded] using success
        simpa [candidateLevels, excluded] using
          ih (level + 1) slot used values nextSlot recursive

/-- First-pass count and actual completed second-pass slots agree without an
assumption about the desired values or about unexecuted arithmetic calls. -/
theorem count_fill_agree (reservation : Arena.Reservation) (keepCandidate : Nat → Bool)
    (make : Nat → Nat → Outcome NatOperand) (remaining level count used : Nat)
    (total : Nat) (values : List NatOperand) (nextSlot : Nat)
    (counted : countLevels keepCandidate remaining level count = .ok total)
    (filled : (fillLevels reservation keepCandidate make remaining level count used).result =
      .ok (values, nextSlot)) : nextSlot = total := by
  have countEq := countLevels_success keepCandidate remaining level count total counted
  have slotEq : nextSlot = count + (candidateLevels keepCandidate remaining level).length := by
    clear counted countEq
    induction remaining generalizing level count used values nextSlot with
    | zero =>
        have same : ([], count) = (values, nextSlot) := by
          simpa [fillLevels, unchanged] using filled
        simpa [candidateLevels] using (congrArg Prod.snd same).symm
    | succ remaining ih =>
        by_cases included : keepCandidate level = true
        · simp only [fillLevels, included, ↓reduceIte] at filled
          obtain ⟨value, made, continued⟩ := (bind_result_ok _ _ _).mp filled
          change (bind (fillLevels reservation keepCandidate make remaining (level + 1)
            (count + 1) (make level used).used)
            (fun rest cursor => unchanged cursor (.ok (value :: rest.1, rest.2)))).result =
            .ok (values, nextSlot) at continued
          obtain ⟨rest, recursive, returned⟩ := (bind_result_ok _ _ _).mp continued
          have same : (value :: rest.1, rest.2) = (values, nextSlot) := by
            simpa [unchanged] using returned
          have slots := ih (level + 1) (count + 1) (make level used).used rest.1 rest.2 recursive
          have nextEq : rest.2 = nextSlot := congrArg Prod.snd same
          simp only [candidateLevels, included, ↓reduceIte, List.length_cons]
          omega
        · have excluded : keepCandidate level = false := Bool.eq_false_iff.mpr included
          have recursive : (fillLevels reservation keepCandidate make remaining (level + 1) count used).result =
              .ok (values, nextSlot) := by simpa [fillLevels, excluded] using filled
          simpa [candidateLevels, excluded] using
            ih (level + 1) count used values nextSlot recursive
  omega

theorem length_success (index : NatOperand) (count : Nat)
    (success : length index = .ok count) :
    count = depth index ∧ 0 < count ∧ 2 ≤ index.value := by
  have erased := length_erase index
  rw [success] at erased
  have pinned : Ssz.gindexLength index.value = .ok count := by
    simpa [eraseResult] using erased.symm
  obtain ⟨same, valid⟩ := pinned_length_ok index.value count pinned
  refine ⟨by simpa [depth_value] using same, ?_, valid⟩
  have positive : 1 ≤ index.value.log2 :=
    (Nat.le_log2 (by omega)).mpr (by simpa using valid)
  omega

theorem arithmetic_shr_value (index : NatOperand) (level base capacity used : Nat)
    (value : NatOperand)
    (success : (arithmetic used (NatShift.shr index level base capacity used)).result = .ok value) :
    value.value = index.value >>> level := by
  have child : (NatShift.shr index level base capacity used).result = .ok value := by
    cases observed : (NatShift.shr index level base capacity used).result with
    | error reason => simp [arithmetic, observed, Except.mapError] at success
    | ok result => simpa [arithmetic, observed, Except.mapError] using success
  exact NatShift.shr_value index level base capacity used value child

/-- Successful physical path construction refines the pinned leaf-up path. -/
theorem pathIndices_success (index : NatOperand) (base capacity used : Nat) (result : NatSlice)
    (success : (pathIndices index base capacity used).result = .ok result) :
    Ssz.getPathIndices index.value = .ok (result.values.map NatOperand.value) := by
  unfold pathIndices at success
  obtain ⟨count, measured, continued⟩ := (bind_result_ok _ _ _).mp success
  have measured' : length index = .ok count := measured
  simp only [unchanged] at continued
  split at continued
  · simp at continued
  · obtain ⟨reservation, reserved, continued⟩ := (bind_result_ok _ _ _).mp continued
    obtain ⟨filled, filledEq, returned⟩ := (bind_result_ok _ _ _).mp continued
    have same : (⟨filled.1, reservation⟩ : NatSlice) = result := by
      simpa [unchanged] using returned
    cases same
    obtain ⟨values, slots⟩ := fillLevels_success reservation (fun _ => true)
      (fun level cursor => arithmetic cursor (NatShift.shr index level base capacity cursor))
      (fun level => index.value >>> level)
      (fun level cursor value h => arithmetic_shr_value index level base capacity cursor value h)
      count 0 0 (reserveNats count base capacity used).used filled.1 filled.2 filledEq
    have erased := length_erase index
    rw [measured'] at erased
    have pinned : Ssz.gindexLength index.value = .ok count := by
      simpa [eraseResult] using erased.symm
    rw [candidateLevels_true] at values
    simpa [Ssz.getPathIndices, pinned, Bind.bind, Except.bind, Pure.pure, Except.pure,
      List.range_eq_range'] using
      congrArg (Except.ok (ε := Ssz.Err)) values.symm

/-- Count preflight establishes every pinned path before any outer reservation. -/
theorem countPaths_success (indices : List NatOperand) (count total : Nat)
    (success : countPaths indices count = .ok total) :
    Ssz.collectPathIndices (indices.map NatOperand.value) =
      .ok (claimPaths (indices.map NatOperand.value)) ∧
    total = count + (claimPaths (indices.map NatOperand.value)).length := by
  induction indices generalizing count total with
  | nil =>
      have same : count = total := by simpa [countPaths] using success
      simp [Ssz.collectPathIndices, claimPaths, same]
  | cons index rest ih =>
      cases measured : length index with
      | error reason => simp [countPaths, measured, Bind.bind, Except.bind] at success
      | ok amount =>
          by_cases amountBound : amount < 2^64
          · by_cases totalBound : count + amount < 2^64
            · have recursive : countPaths rest (count + amount) = .ok total := by
                simp [countPaths, measured, Nat.not_le.mpr amountBound,
                  Nat.not_le.mpr totalBound, Bind.bind, Except.bind] at success
                exact success
              obtain ⟨collected, totalEq⟩ := ih (count + amount) total recursive
              have erased := length_erase index
              rw [measured] at erased
              have pinned : Ssz.gindexLength index.value = .ok amount := by
                simpa [eraseResult] using erased.symm
              have depthEq := (length_success index amount measured).1
              constructor
              · simp [Ssz.collectPathIndices, Ssz.getPathIndices, pinned, collected,
                  claimPaths, Bind.bind, Except.bind, Pure.pure, Except.pure, depthEq, depth_value]
              · simp only [List.map_cons, claimPaths, List.flatMap_cons, List.length_append,
                  List.length_map, List.length_range]
                change total = count + (index.value.log2 +
                  (claimPaths (rest.map NatOperand.value)).length)
                rw [depth_value] at depthEq
                omega
            · simp [countPaths, measured, Nat.not_le.mpr amountBound,
                show count + amount ≥ 2^64 by omega, Bind.bind, Except.bind] at success <;>
                cases success
          · simp [countPaths, measured, show amount ≥ 2^64 by omega,
              Bind.bind, Except.bind] at success

theorem fillClaims_path_success (indices pending : List NatOperand)
    (reservation : Arena.Reservation) (base capacity claim slot used : Nat)
    (values : List NatOperand) (nextSlot : Nat)
    (success : (fillClaims indices false reservation base capacity pending claim slot used).result =
      .ok (values, nextSlot)) :
    values.map NatOperand.value = claimPaths (pending.map NatOperand.value) ∧
      nextSlot = slot + (claimPaths (pending.map NatOperand.value)).length := by
  induction pending generalizing claim slot used values nextSlot with
  | nil =>
      have same : ([], slot) = (values, nextSlot) := by
        simpa [fillClaims, unchanged] using success
      cases same
      simp [claimPaths]
  | cons index rest ih =>
      simp only [fillClaims, Bool.false_eq_true, ↓reduceIte] at success
      obtain ⟨first, firstEq, continued⟩ := (bind_result_ok _ _ _).mp success
      obtain ⟨second, secondEq, returned⟩ := (bind_result_ok _ _ _).mp continued
      have same : (first.1 ++ second.1, second.2) = (values, nextSlot) := by
        simpa [unchanged] using returned
      cases same
      obtain ⟨firstValues, firstSlots⟩ := fillLevels_success reservation (fun _ => true)
        (fun level cursor => arithmetic cursor (NatShift.shr index level base capacity cursor))
        (fun level => index.value >>> level)
        (fun level cursor value h => arithmetic_shr_value index level base capacity cursor value h)
        (depth index) 0 slot used first.1 first.2 firstEq
      obtain ⟨restValues, restSlots⟩ := ih (claim + 1) first.2 _ second.1 second.2 secondEq
      rw [candidateLevels_true] at firstValues firstSlots
      constructor
      · simp only [List.map_append, firstValues, restValues, List.map_cons, claimPaths,
          List.flatMap_cons, depth_value, List.range_eq_range']
      · simp only [List.map_cons, claimPaths, List.flatMap_cons, List.length_append,
          List.length_map, List.length_range]
        simp only [List.length_range', depth_value] at firstSlots
        change second.2 = slot + (index.value.log2 +
          (claimPaths (rest.map NatOperand.value)).length)
        omega

/-- Flattening preserves request order, including repeated and nested requests. -/
theorem collectPathIndices_success (indices : List NatOperand) (base capacity used : Nat)
    (result : NatSlice)
    (success : (collectPathIndices indices base capacity used).result = .ok result) :
    Ssz.collectPathIndices (indices.map NatOperand.value) =
      .ok (result.values.map NatOperand.value) := by
  unfold collectPathIndices at success
  obtain ⟨count, counted, continued⟩ := (bind_result_ok _ _ _).mp success
  obtain ⟨reservation, reserved, continued⟩ := (bind_result_ok _ _ _).mp continued
  obtain ⟨filled, filledEq, returned⟩ := (bind_result_ok _ _ _).mp continued
  have same : (⟨filled.1, reservation⟩ : NatSlice) = result := by
    simpa [unchanged] using returned
  cases same
  have paths := (countPaths_success indices 0 count counted).1
  have values := (fillClaims_path_success indices indices reservation base capacity 0 0 _
    filled.1 filled.2 filledEq).1
  simpa [values] using paths

/-- The full helper count is the exact number of slots completed by a successful
second pass, independent of the representation chosen by each arithmetic call. -/
theorem countHelpers_fill_agree (indices pending : List NatOperand)
    (reservation : Arena.Reservation) (base capacity claim slot used total : Nat)
    (values : List NatOperand) (nextSlot : Nat)
    (counted : countHelpers indices pending claim slot = .ok total)
    (filled : (fillClaims indices true reservation base capacity pending claim slot used).result =
      .ok (values, nextSlot)) : nextSlot = total ∧ values.length = total - slot := by
  have countEq := countHelpers_count indices pending claim slot total counted
  obtain ⟨lengthEq, slotEq, completed⟩ :=
    (fillClaims_prefix indices true reservation base capacity pending claim slot used).success
      values nextSlot filled
  omega

theorem countPaths_fill_agree (indices pending : List NatOperand)
    (reservation : Arena.Reservation) (base capacity claim slot used total : Nat)
    (values : List NatOperand) (nextSlot : Nat)
    (counted : countPaths pending slot = .ok total)
    (filled : (fillClaims indices false reservation base capacity pending claim slot used).result =
      .ok (values, nextSlot)) : nextSlot = total ∧ values.length = total - slot := by
  have countEq := countPaths_count indices pending claim slot total counted
  obtain ⟨lengthEq, slotEq, completed⟩ :=
    (fillClaims_prefix indices false reservation base capacity pending claim slot used).success
      values nextSlot filled
  omega

end SszNative.Indices

import SszIndicesFrontierSemanticBuild

set_option autoImplicit false

namespace SszX86.IndicesFrontierSort
open SszNative SszNative.Indices

/-- Numeric uniqueness of the retained frontier makes comparison injective on
its actual Nat records, without requiring canonical input representations. -/
theorem equal_value_of_unique_members (values : List NatOperand)
    (unique : (values.map NatOperand.value).Nodup)
    (left right : NatOperand) (leftMember : left ∈ values) (rightMember : right ∈ values)
    (same : left.value = right.value) : left = right := by
  induction values with
  | nil => simp at leftMember
  | cons first rest ih =>
    obtain ⟨absent, restUnique⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp leftMember with firstLeft | leftMember
    · subst left
      rcases List.mem_cons.mp rightMember with firstRight | rightMember
      · exact firstRight.symm
      · have present : right.value ∈ rest.map NatOperand.value :=
          List.mem_map.mpr ⟨right, rightMember, rfl⟩
        rw [← same] at present
        exact False.elim (absent present)
    · rcases List.mem_cons.mp rightMember with firstRight | rightMember
      · subst right
        have present : left.value ∈ rest.map NatOperand.value :=
          List.mem_map.mpr ⟨left, leftMember, rfl⟩
        rw [same] at present
        exact False.elim (absent present)
      · exact ih restUnique leftMember rightMember

/-- Agreement by numeric value lifts to exact stored Nat operands when both
lists consist of records from the same unique retained frontier. -/
theorem records_eq_of_values_eq (original left right : List NatOperand)
    (unique : (original.map NatOperand.value).Nodup)
    (leftMembers : ∀ value ∈ left, value ∈ original)
    (rightMembers : ∀ value ∈ right, value ∈ original)
    (same : left.map NatOperand.value = right.map NatOperand.value) : left = right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons first rest => simp at same
  | cons first rest ih =>
    cases right with
    | nil => simp at same
    | cons other remaining =>
      have equalities : first.value = other.value ∧
          rest.map NatOperand.value = remaining.map NatOperand.value := by
        simpa only [List.map_cons, List.cons.injEq] using same
      have heads := equal_value_of_unique_members original unique first other
        (leftMembers first (by simp)) (rightMembers other (by simp)) equalities.1
      have tails := ih remaining
        (fun value member => leftMembers value (List.mem_cons_of_mem first member))
        (fun value member => rightMembers value (List.mem_cons_of_mem other member)) equalities.2
      exact congrArg₂ List.cons heads tails

/-- This is a postcondition consequence, not an assumed execution of either
native sort. Their machine proofs must separately establish permutation and
descending order. Numeric uniqueness then determines the exact model result,
including the borrowed pointers and noncanonical representations. -/
theorem exact_frontier_sort (original sorted : List NatOperand)
    (unique : (original.map NatOperand.value).Nodup)
    (permuted : sorted.Perm original)
    (ordered : (sorted.map NatOperand.value).Pairwise (fun a b => b ≤ a)) :
    sorted = original.mergeSort (fun left right => right.value ≤ left.value) := by
  have numeric := permuted.map NatOperand.value
  have sortedUnique := numeric.symm.nodup unique
  have referenceUnique := (List.mergeSort_perm (original.map NatOperand.value)
    (fun left right => right ≤ left)).symm.nodup unique
  have numericSame : sorted.map NatOperand.value =
      (original.map NatOperand.value).mergeSort (fun left right => right ≤ left) := by
    apply descending_ext _ _ sortedUnique referenceUnique ordered (descending_mergeSort _)
    intro value
    simpa only [List.mem_mergeSort] using numeric.mem_iff
  apply records_eq_of_values_eq original sorted
    (original.mergeSort (fun left right => right.value ≤ left.value)) unique
  · intro value member
    exact permuted.mem_iff.mp member
  · intro value member
    exact List.mem_mergeSort.mp member
  · rw [values_mergeSort]
    exact numericSame

/-- Successful source fill derives numeric uniqueness from the original
validated request. The sorting proof need not assume it as a public premise. -/
theorem filled_frontier_unique (indices : List NatOperand)
    (reservation : Arena.Reservation) (base capacity used : Nat)
    (physical : ∀ index ∈ indices, index.words.length < 2 ^ 64)
    (accepted : rejectRelated indices = .ok ())
    (values : List NatOperand) (slot : Nat)
    (filled : (fillClaims indices true reservation base capacity indices 0 0 used).result =
      .ok (values, slot)) : (values.map NatOperand.value).Nodup := by
  have exactValues := fillClaims_helpers_values indices indices reservation base capacity
    0 0 used physical values slot filled
  have candidateValues : values.map NatOperand.value = helperCandidates indices := by
    rw [exactValues]
    simp only [helperCandidates, helperCandidateKeys, List.map_flatMap,
      List.map_map, Function.comp_def, helperCandidateValue]
  rw [candidateValues]
  exact helperCandidates_nodup indices physical (rejectRelated_valid indices accepted)

end SszX86.IndicesFrontierSort

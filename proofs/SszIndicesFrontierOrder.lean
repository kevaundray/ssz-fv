import SszIndicesTypes
import SszIndicesPinnedFrontier

set_option autoImplicit false

namespace SszNative.Indices

/-- In-place native sorting and the pinned merge sort agree extensionally on a
unique frontier. No claim of equal intermediate order or equal representations
of equal-valued inputs is needed. -/
theorem descending_ext (left right : List Nat)
    (leftUnique : left.Nodup) (rightUnique : right.Nodup)
    (leftOrdered : left.Pairwise (fun a b => b ≤ a))
    (rightOrdered : right.Pairwise (fun a b => b ≤ a))
    (members : ∀ value, value ∈ left ↔ value ∈ right) : left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons first rest =>
          have absent := (members first).mpr (by simp)
          simp at absent
  | cons first rest ih =>
      cases right with
      | nil =>
          have absent := (members first).mp (by simp)
          simp at absent
      | cons other remaining =>
          obtain ⟨firstNot, restUnique⟩ := List.nodup_cons.mp leftUnique
          obtain ⟨otherNot, remainingUnique⟩ := List.nodup_cons.mp rightUnique
          obtain ⟨firstAbove, restOrdered⟩ := List.pairwise_cons.mp leftOrdered
          obtain ⟨otherAbove, remainingOrdered⟩ := List.pairwise_cons.mp rightOrdered
          have firstLe : first ≤ other := by
            rcases List.mem_cons.mp ((members first).mp (by simp)) with same | member
            · omega
            · exact otherAbove first member
          have otherLe : other ≤ first := by
            rcases List.mem_cons.mp ((members other).mpr (by simp)) with same | member
            · omega
            · exact firstAbove other member
          have same : other = first := by omega
          subst other
          congr 1
          apply ih remaining restUnique remainingUnique restOrdered remainingOrdered
          intro value
          constructor
          · intro member
            rcases List.mem_cons.mp ((members value).mp (List.mem_cons_of_mem _ member)) with same | found
            · subst value
              exact False.elim (firstNot member)
            · exact found
          · intro member
            rcases List.mem_cons.mp ((members value).mpr (List.mem_cons_of_mem _ member)) with same | found
            · subst value
              exact False.elim (otherNot member)
            · exact found

theorem descending_mergeSort (values : List Nat) :
    (values.mergeSort (fun a b => b ≤ a)).Pairwise (fun a b => b ≤ a) := by
  have ordered := List.pairwise_mergeSort
    (le := fun a b : Nat => decide (b ≤ a))
    (by intro a b c first second; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) values
  simpa only [decide_eq_true_eq] using ordered

theorem descending_mergeSort_ext (left right : List Nat)
    (leftUnique : left.Nodup) (rightUnique : right.Nodup)
    (members : ∀ value, value ∈ left ↔ value ∈ right) :
    left.mergeSort (fun a b => b ≤ a) = right.mergeSort (fun a b => b ≤ a) := by
  apply descending_ext
  · exact (List.mergeSort_perm _ _).symm.nodup leftUnique
  · exact (List.mergeSort_perm _ _).symm.nodup rightUnique
  · exact descending_mergeSort left
  · exact descending_mergeSort right
  · intro value
    simpa only [List.mem_mergeSort] using members value

theorem values_mergeSort (values : List NatOperand) :
    (values.mergeSort (fun left right => right.value ≤ left.value)).map NatOperand.value =
      (values.map NatOperand.value).mergeSort (fun left right => right ≤ left) := by
  exact List.map_mergeSort (by intro a _ b _; rfl)

/-- Any native unique candidate enumeration of the same frontier gives exactly
the pinned helper pairing after descending numeric sort. -/
theorem sorted_frontier_eq (indices helpers candidates : List Nat)
    (pinned : Ssz.getHelperIndices indices = .ok helpers)
    (unique : candidates.Nodup)
    (members : ∀ node, node ∈ candidates ↔
      node ∈ (claimPaths indices).map Ssz.gindexSibling ∧
      node ∉ claimPaths indices) :
    candidates.mergeSort (fun a b => b ≤ a) = helpers := by
  have same : ∀ node, node ∈ candidates ↔ node ∈ helpers := by
    intro node
    exact (members node).trans (pinned_helper_frontier pinned node).symm
  have sorted : helpers.Pairwise (fun a b => b ≤ a) := by
    unfold Ssz.getHelperIndices at pinned
    cases rejected : Ssz.rejectRelated indices with
    | error reason => simp [rejected, Bind.bind, Except.bind] at pinned
    | ok accepted =>
        cases accepted
        cases collected : Ssz.collectPathIndices indices with
        | error reason => simp [rejected, collected, Bind.bind, Except.bind] at pinned
        | ok paths =>
            simp [rejected, collected, Bind.bind, Except.bind, Pure.pure, Except.pure] at pinned
            subst helpers
            exact descending_mergeSort _
  apply descending_ext _ _ ((List.mergeSort_perm _ _).symm.nodup unique)
    (pinned_helper_nodup pinned) (descending_mergeSort _) sorted
  intro node
  simpa only [List.mem_mergeSort] using same node

end SszNative.Indices

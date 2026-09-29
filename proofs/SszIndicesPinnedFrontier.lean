import SszIndicesTypes
import Ssz.Proofs.Merkle.Gindex

set_option autoImplicit false

namespace SszNative.Indices

/-- Pure view of the pinned path definition. Kept independent of Merkle-tree
hashing proofs: index/path refinement does not require a SHA/tree hypothesis. -/
def claimPaths (indices : List Nat) : List Nat :=
  indices.flatMap fun index =>
    (List.range index.log2).map fun level => index >>> level

theorem pinned_length_ok (index count : Nat)
    (accepted : Ssz.gindexLength index = .ok count) :
    count = index.log2 ∧ 2 ≤ index := by
  by_cases invalid : index < 1
  · simp [Ssz.gindexLength, Ssz.gindexDepth, invalid, Bind.bind, Except.bind] at accepted
  · by_cases root : index.log2 = 0
    · simp [Ssz.gindexLength, Ssz.gindexDepth, invalid, root, Bind.bind, Except.bind] at accepted
    · have equal : index.log2 = count := by
        simpa [Ssz.gindexLength, Ssz.gindexDepth, invalid, root, Bind.bind, Except.bind] using accepted
      refine ⟨equal.symm, ?_⟩
      by_cases below : 2 ≤ index
      · exact below
      · have one : index = 1 := by omega
        exact False.elim (root (by rw [one]; decide))

theorem pinned_collect_info {indices paths : List Nat}
    (collected : Ssz.collectPathIndices indices = .ok paths) :
    paths = claimPaths indices ∧ ∀ index ∈ indices, 2 ≤ index := by
  induction indices generalizing paths with
  | nil =>
      simp [Ssz.collectPathIndices] at collected
      subst paths
      simp [claimPaths]
  | cons index rest ih =>
      unfold Ssz.collectPathIndices at collected
      cases measured : Ssz.gindexLength index with
      | error reason =>
          simp [Ssz.getPathIndices, measured, Bind.bind, Except.bind] at collected
      | ok count =>
          obtain ⟨same, valid⟩ := pinned_length_ok index count measured
          subst count
          cases rec : Ssz.collectPathIndices rest with
          | error reason =>
              simp [Ssz.getPathIndices, measured, rec, Bind.bind, Except.bind,
                Pure.pure, Except.pure] at collected
          | ok remaining =>
              obtain ⟨shape, restValid⟩ := ih rec
              simp [Ssz.getPathIndices, measured, rec, Bind.bind, Except.bind,
                Pure.pure, Except.pure] at collected
              constructor
              · rw [← collected, shape]
                rfl
              · intro value member
                rcases List.mem_cons.mp member with equal | member
                · subst value
                  exact valid
                · exact restValid value member

theorem eraseDups_nodup (values : List Nat) : values.eraseDups.Nodup := by
  cases values with
  | nil => simp
  | cons first rest =>
      rw [List.eraseDups_cons, List.nodup_cons]
      refine ⟨?_, eraseDups_nodup (rest.filter fun value => !value == first)⟩
      simp
termination_by values.length
decreasing_by
  have bounded := List.length_filter_le (fun value => !value == first) rest
  simp_all
  omega

theorem pinned_helper_nodup {indices helpers : List Nat}
    (built : Ssz.getHelperIndices indices = .ok helpers) : helpers.Nodup := by
  unfold Ssz.getHelperIndices at built
  cases accepted : Ssz.rejectRelated indices with
  | error reason => simp [accepted, Bind.bind, Except.bind] at built
  | ok checked =>
      cases checked
      cases collected : Ssz.collectPathIndices indices with
      | error reason => simp [accepted, collected, Bind.bind, Except.bind] at built
      | ok paths =>
          simp [accepted, collected, Bind.bind, Except.bind, Pure.pure, Except.pure] at built
          subst helpers
          exact (List.mergeSort_perm _ _).symm.nodup
            ((eraseDups_nodup (paths.map Ssz.gindexSibling)).filter _)

theorem pinned_helper_frontier {indices helpers : List Nat}
    (built : Ssz.getHelperIndices indices = .ok helpers) :
    ∀ node, node ∈ helpers ↔
      node ∈ (claimPaths indices).map Ssz.gindexSibling ∧ node ∉ claimPaths indices := by
  unfold Ssz.getHelperIndices at built
  cases accepted : Ssz.rejectRelated indices with
  | error reason => simp [accepted, Bind.bind, Except.bind] at built
  | ok checked =>
      cases checked
      cases collected : Ssz.collectPathIndices indices with
      | error reason => simp [accepted, collected, Bind.bind, Except.bind] at built
      | ok paths =>
          have shape := (pinned_collect_info collected).1
          simp [accepted, collected, Bind.bind, Except.bind, Pure.pure, Except.pure] at built
          subst helpers
          intro node
          simp [List.mem_mergeSort, List.mem_filter, List.mem_eraseDups, shape]

theorem shiftRight_le (index level : Nat) : index >>> level ≤ index := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_le_self _ _

theorem path_shift_positive {index level : Nat} (named : 1 ≤ index)
    (inside : level < index.log2) : 2 ≤ index >>> level := by
  have reaches := Ssz.shiftRight_depth named
  have distance : level + 1 + (index.log2 - (level + 1)) = index.log2 := by omega
  have upper : 1 ≤ index >>> (level + 1) := by
    have smaller := shiftRight_le (index >>> (level + 1)) (index.log2 - (level + 1))
    rw [← Nat.shiftRight_add, distance, reaches] at smaller
    exact smaller
  rw [Ssz.shiftRight_succ] at upper
  omega

theorem pinned_sibling_log2 (index : Nat) (below : 2 ≤ index) :
    (Ssz.gindexSibling index).log2 = index.log2 := by
  have halves := Ssz.gindexSibling_half index
  have siblingBelow : 2 ≤ Ssz.gindexSibling index := by omega
  rw [Nat.log2_def (Ssz.gindexSibling index), Nat.log2_def index]
  simp only [siblingBelow, below, ↓reduceIte, halves]

end SszNative.Indices

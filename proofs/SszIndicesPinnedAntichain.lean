import SszIndicesPinnedFrontier

set_option autoImplicit false

namespace SszNative.Indices

private theorem pinned_reject_nonempty {indices : List Nat}
    (accepted : Ssz.rejectRelated indices = .ok ()) : indices ≠ [] := by
  intro empty
  subst indices
  simp [Ssz.rejectRelated_empty] at accepted

private theorem pinned_helper_accepted {indices helpers : List Nat}
    (built : Ssz.getHelperIndices indices = .ok helpers) :
    Ssz.rejectRelated indices = .ok () := by
  unfold Ssz.getHelperIndices at built
  cases checked : Ssz.rejectRelated indices with
  | error reason => simp [checked, Bind.bind, Except.bind] at built
  | ok accepted => cases accepted; rfl

theorem pinned_helper_info {indices helpers : List Nat}
    (built : Ssz.getHelperIndices indices = .ok helpers) :
    indices ≠ [] ∧ (∀ index ∈ indices, 2 ≤ index) ∧
      ∀ index, index ∈ helpers ↔
        index ∈ (claimPaths indices).map Ssz.gindexSibling ∧ index ∉ claimPaths indices := by
  refine ⟨pinned_reject_nonempty (pinned_helper_accepted built), ?_, pinned_helper_frontier built⟩
  unfold Ssz.getHelperIndices at built
  cases accepted : Ssz.rejectRelated indices with
  | error reason => simp [accepted, Bind.bind, Except.bind] at built
  | ok checked =>
      cases checked
      cases collected : Ssz.collectPathIndices indices with
      | error reason => simp [accepted, collected, Bind.bind, Except.bind] at built
      | ok paths => exact (pinned_collect_info collected).2

private theorem pinned_claim_mem {indices : List Nat}
    (valid : ∀ index ∈ indices, 2 ≤ index) {index : Nat} (claimed : index ∈ indices) :
    index ∈ claimPaths indices := by
  have positive : 0 < index.log2 := by
    have unfolded := Nat.log2_def index
    simp only [valid index claimed, ↓reduceIte] at unfolded
    omega
  exact List.mem_flatMap.mpr ⟨index, claimed,
    List.mem_map.mpr ⟨0, List.mem_range.mpr positive, by simp⟩⟩

private theorem eraseDups_sublist (values : List Nat) : values.eraseDups.Sublist values := by
  cases values with
  | nil => simp
  | cons first rest =>
      rw [List.eraseDups_cons]
      exact List.Sublist.cons_cons _
        ((eraseDups_sublist (rest.filter fun value => !value == first)).trans List.filter_sublist)
termination_by values.length
decreasing_by
  have bounded := List.length_filter_le (fun value => !value == first) rest
  simp_all
  omega

private theorem pinned_reject_nodup {indices : List Nat}
    (accepted : Ssz.rejectRelated indices = .ok ()) : indices.Nodup := by
  by_cases same : indices.eraseDups.length = indices.length
  · have unchanged := (eraseDups_sublist indices).eq_of_length same
    rw [← unchanged]
    exact eraseDups_nodup indices
  · cases indices with
    | nil => simp at same
    | cons first rest =>
        simp only [List.length_cons] at same
        dsimp only [Ssz.rejectRelated, Bind.bind, Except.bind, Pure.pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at accepted
        simp [same] at accepted

theorem pinned_helper_all_nodup {indices helpers : List Nat}
    (built : Ssz.getHelperIndices indices = .ok helpers) : (indices ++ helpers).Nodup := by
  obtain ⟨_, valid, frontier⟩ := pinned_helper_info built
  rw [List.nodup_append]
  refine ⟨pinned_reject_nodup (pinned_helper_accepted built), pinned_helper_nodup built, ?_⟩
  intro claim claimed helper supplied same
  subst helper
  exact (frontier claim |>.mp supplied).2 (pinned_claim_mem valid claimed)

private theorem pinned_paths_bounds {indices : List Nat}
    (valid : ∀ index ∈ indices, 2 ≤ index) {index : Nat}
    (member : index ∈ claimPaths indices) : 2 ≤ index := by
  obtain ⟨claim, claimed, shifted⟩ := List.mem_flatMap.mp member
  obtain ⟨level, inside, same⟩ := List.mem_map.mp shifted
  subst index
  exact path_shift_positive (by have := valid claim claimed; omega) (List.mem_range.mp inside)

private theorem pinned_paths_parent {indices : List Nat}
    (valid : ∀ index ∈ indices, 2 ≤ index) {index : Nat}
    (member : index ∈ claimPaths indices) : index / 2 = 1 ∨ index / 2 ∈ claimPaths indices := by
  obtain ⟨claim, claimed, shifted⟩ := List.mem_flatMap.mp member
  obtain ⟨level, inside, same⟩ := List.mem_map.mp shifted
  rw [← same, ← Ssz.shiftRight_succ]
  have below := List.mem_range.mp inside
  by_cases last : level + 1 = claim.log2
  · left
    rw [last, Ssz.shiftRight_depth (by have := valid claim claimed; omega)]
  · right
    exact List.mem_flatMap.mpr ⟨claim, claimed,
      List.mem_map.mpr ⟨level + 1, List.mem_range.mpr (by omega), rfl⟩⟩

theorem pinned_helper_sibling {indices helpers : List Nat}
    (built : Ssz.getHelperIndices indices = .ok helpers) {index : Nat}
    (member : index ∈ claimPaths indices ∨ index ∈ helpers) :
    2 ≤ index ∧
      (Ssz.gindexSibling index ∈ claimPaths indices ∨ Ssz.gindexSibling index ∈ helpers) ∧
      (index / 2 = 1 ∨ index / 2 ∈ claimPaths indices) := by
  obtain ⟨_, valid, frontier⟩ := pinned_helper_info built
  rcases member with path | helper
  · refine ⟨pinned_paths_bounds valid path, ?_, pinned_paths_parent valid path⟩
    by_cases onPath : Ssz.gindexSibling index ∈ claimPaths indices
    · exact Or.inl onPath
    · exact Or.inr ((frontier _).mpr ⟨List.mem_map.mpr ⟨index, path, rfl⟩, onPath⟩)
  · obtain ⟨mapped, _⟩ := (frontier index).mp helper
    obtain ⟨sibling, path, same⟩ := List.mem_map.mp mapped
    subst index
    have positive := pinned_paths_bounds valid path
    have half := Ssz.gindexSibling_half sibling
    refine ⟨by omega, ?_, ?_⟩
    · exact Or.inl (by simpa only [Ssz.gindexSibling_sibling] using path)
    · rw [half]
      exact pinned_paths_parent valid path

private theorem pinned_reject_ancestors {indices ancestors : List Nat} {claim : Nat}
    (accepted : Ssz.rejectAncestors indices claim ancestors = .ok ()) :
    ∀ ancestor ∈ ancestors, ancestor ∉ indices := by
  induction ancestors with
  | nil => simp
  | cons first rest ih =>
      by_cases present : first ∈ indices
      · simp [Ssz.rejectAncestors, present, Bind.bind, Except.bind, throw, throwThe,
          MonadExceptOf.throw] at accepted
      · have tailAccepted : Ssz.rejectAncestors indices claim rest = .ok () := by
          simpa [Ssz.rejectAncestors, present, Bind.bind, Except.bind, Pure.pure, Except.pure]
            using accepted
        intro ancestor member
        rcases List.mem_cons.mp member with same | member
        · simpa [same] using present
        · exact ih tailAccepted ancestor member

private theorem pinned_reject_paths {indices pending : List Nat}
    (accepted : Ssz.rejectClaimPaths indices pending = .ok ()) :
    ∀ claim ∈ pending, ∃ path, Ssz.getPathIndices claim = .ok path ∧
      ∀ ancestor ∈ path.drop 1, ancestor ∉ indices := by
  induction pending with
  | nil => simp
  | cons first rest ih =>
      cases pathEq : Ssz.getPathIndices first with
      | error reason => simp [Ssz.rejectClaimPaths, pathEq, Bind.bind, Except.bind] at accepted
      | ok path =>
          cases checked : Ssz.rejectAncestors indices first path.tail with
          | error reason =>
              simp [Ssz.rejectClaimPaths, pathEq, checked, Bind.bind, Except.bind] at accepted
          | ok checkedValue =>
              cases checkedValue
              have tailAccepted : Ssz.rejectClaimPaths indices rest = .ok () := by
                simpa [Ssz.rejectClaimPaths, pathEq, checked, Bind.bind, Except.bind] using accepted
              intro claim member
              rcases List.mem_cons.mp member with same | member
              · subst claim
                exact ⟨path, pathEq, pinned_reject_ancestors (by simpa using checked)⟩
              · exact ih tailAccepted claim member

private theorem pinned_related_paths {indices : List Nat}
    (accepted : Ssz.rejectRelated indices = .ok ()) :
    Ssz.rejectClaimPaths indices indices = .ok () := by
  have nonempty := pinned_reject_nonempty accepted
  by_cases same : indices.eraseDups.length = indices.length
  · simpa [Ssz.rejectRelated, nonempty, same, Bind.bind, Except.bind, Pure.pure, Except.pure]
      using accepted
  · dsimp only [Ssz.rejectRelated, Bind.bind, Except.bind, Pure.pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw] at accepted
    simp [nonempty, same] at accepted

private theorem pinned_reject_strict_shift {indices : List Nat}
    (accepted : Ssz.rejectRelated indices = .ok ()) {claim step : Nat}
    (claimed : claim ∈ indices) (positive : 0 < step) (below : step < claim.log2) :
    claim >>> step ∉ indices := by
  obtain ⟨path, pathEq, excludes⟩ :=
    pinned_reject_paths (pinned_related_paths accepted) claim claimed
  cases measured : Ssz.gindexLength claim with
  | error reason => simp [Ssz.getPathIndices, measured, Bind.bind, Except.bind] at pathEq
  | ok count =>
      have same := (pinned_length_ok claim count measured).1
      subst count
      simp [Ssz.getPathIndices, measured, Bind.bind, Except.bind, Pure.pure, Except.pure] at pathEq
      subst path
      apply excludes
      rw [← List.map_drop]
      apply List.mem_map.mpr
      refine ⟨step, List.mem_drop_iff_getElem.mpr ?_, rfl⟩
      refine ⟨step - 1, by simp; omega, ?_⟩
      simp only [List.getElem_range]
      omega

private theorem pinned_shift_below_depth {claim step : Nat} (named : 1 ≤ claim)
    (below : 2 ≤ claim >>> step) : step < claim.log2 := by
  by_cases inside : step < claim.log2
  · exact inside
  have distance : claim.log2 + (step - claim.log2) = step := by omega
  have upper : (claim >>> claim.log2) >>> (step - claim.log2) ≤ 1 := by
    rw [Ssz.shiftRight_depth named]
    exact shiftRight_le 1 (step - claim.log2)
  rw [← Nat.shiftRight_add, distance] at upper
  omega

private theorem pinned_sibling_strict_shift (index step : Nat) (positive : 0 < step) :
    Ssz.gindexSibling index >>> step = index >>> step := by
  have distance : step - 1 + 1 = step := by omega
  rw [← distance, Nat.add_comm (step - 1) 1, Nat.shiftRight_add, Nat.shiftRight_add]
  have half := Ssz.gindexSibling_half index
  simpa [Nat.shiftRight_eq_div_pow] using congrArg (fun value => value >>> (step - 1)) half

theorem pinned_helper_antichain {indices helpers : List Nat}
    (built : Ssz.getHelperIndices indices = .ok helpers) :
    ∀ i ∈ indices ++ helpers, ∀ j ∈ indices ++ helpers, ∀ step,
      i >>> step = j → i = j := by
  obtain ⟨_, valid, frontier⟩ := pinned_helper_info built
  have accepted := pinned_helper_accepted built
  intro i supplied j target step shifted
  by_cases zero : step = 0
  · simpa [zero] using shifted
  have positive : 0 < step := by omega
  have jBelow : 2 ≤ j := by
    rcases List.mem_append.mp target with claim | helper
    · exact valid j claim
    · exact (pinned_helper_sibling built (Or.inr helper)).1
  have origin : ∃ claim ∈ indices, ∃ distance, 0 < distance ∧ claim >>> distance = j := by
    rcases List.mem_append.mp supplied with claim | helper
    · exact ⟨i, claim, step, positive, shifted⟩
    · obtain ⟨mapped, _⟩ := (frontier i).mp helper
      obtain ⟨node, path, same⟩ := List.mem_map.mp mapped
      obtain ⟨claim, claimed, member⟩ := List.mem_flatMap.mp path
      obtain ⟨base, _, baseEq⟩ := List.mem_map.mp member
      refine ⟨claim, claimed, base + step, by omega, ?_⟩
      rw [Nat.shiftRight_add, baseEq, ← pinned_sibling_strict_shift node step positive, same]
      exact shifted
  obtain ⟨claim, claimed, distance, strict, reaches⟩ := origin
  have below := pinned_shift_below_depth (by have := valid claim claimed; omega)
    (show 2 ≤ claim >>> distance by omega)
  have onPath : j ∈ claimPaths indices := List.mem_flatMap.mpr
    ⟨claim, claimed, List.mem_map.mpr ⟨distance, List.mem_range.mpr below, reaches⟩⟩
  rcases List.mem_append.mp target with target | target
  · exact False.elim (pinned_reject_strict_shift accepted claimed strict below (reaches ▸ target))
  · exact False.elim (((frontier j).mp target).2 onPath)

end SszNative.Indices

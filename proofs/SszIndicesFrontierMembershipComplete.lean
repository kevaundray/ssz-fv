import SszIndicesFrontierMembership

set_option autoImplicit false

namespace SszNative.Indices

theorem candidate_path_depth (index : NatOperand) (level : Nat)
    (valid : 2 ≤ index.value) (inside : level < depth index) :
    (index.value >>> level).log2 = depth index - level := by
  rw [depth_value] at inside ⊢
  exact shift_log2 index.value level (by omega) (by omega)

/-- An arbitrary path witness is aligned to the candidate's depth, rather than
assuming that the operational prefix comparison already selected it. -/
theorem candidate_path_alignment (index other : NatOperand) (level step : Nat)
    (valid : 2 ≤ index.value) (otherValid : 2 ≤ other.value)
    (inside : level < depth index) (otherInside : step < depth other)
    (same : Ssz.gindexSibling (index.value >>> level) = other.value >>> step) :
    depth index - level ≤ depth other ∧
      step = depth other - (depth index - level) := by
  have below := path_shift_positive (by omega : 1 ≤ index.value)
    (by simpa only [depth_value] using inside)
  have left := sibling_log2 (index.value >>> level) below
  have first := candidate_path_depth index level valid inside
  have second := candidate_path_depth other step otherValid otherInside
  rw [same] at left
  omega

/-- The allocation-free source predicate enumerates exactly the pinned missing
siblings. Minimal request ordinals supply the first occurrence, independently
of whether any candidate has already passed the predicate. -/
theorem helperCandidates_membership (indices : List NatOperand)
    (physical : ∀ index ∈ indices, index.words.length < 2^64)
    (valid : ∀ index ∈ indices, 2 ≤ index.value) (node : Nat) :
    node ∈ helperCandidates indices ↔
      node ∈ (claimPaths (indices.map NatOperand.value)).map Ssz.gindexSibling ∧
      node ∉ claimPaths (indices.map NatOperand.value) := by
  classical
  constructor
  · intro member
    obtain ⟨index, ordinal, level, atOrdinal, inside, retained, value⟩ :=
      (mem_helperCandidates_iff indices node).mp member
    have claimed := List.fst_mem_of_mem_zipIdx atOrdinal
    have criterion := (isHelper_iff indices index ordinal level physical
      (physical index claimed) inside).mp retained
    constructor
    · exact List.mem_map.mpr ⟨index.value >>> level,
        (mem_claimPaths_iff indices _).mpr ⟨index, ordinal, level, atOrdinal, inside, rfl⟩,
        value⟩
    · intro onPath
      obtain ⟨other, otherOrdinal, step, otherMember, otherInside, otherValue⟩ :=
        (mem_claimPaths_iff indices node).mp onPath
      have aligned := candidate_path_alignment index other level step
        (valid index claimed) (valid other (List.fst_mem_of_mem_zipIdx otherMember))
        inside otherInside (value.trans otherValue.symm)
      have excluded := (criterion other otherOrdinal otherMember aligned.1).1
      apply excluded
      rw [← aligned.2]
      exact value.trans otherValue.symm
  · rintro ⟨siblingMember, missing⟩
    obtain ⟨path, pathMember, siblingValue⟩ := List.mem_map.mp siblingMember
    obtain ⟨initial, initialOrdinal, initialLevel, initialMember, initialInside, initialValue⟩ :=
      (mem_claimPaths_iff indices path).mp pathMember
    let occurs (ordinal : Nat) : Prop := ∃ index level,
      (index, ordinal) ∈ indices.zipIdx ∧ level < depth index ∧
        Ssz.gindexSibling (index.value >>> level) = node
    have existsOccurrence : ∃ ordinal, occurs ordinal := by
      exact ⟨initialOrdinal, initial, initialLevel, initialMember, initialInside,
        (congrArg Ssz.gindexSibling initialValue).trans siblingValue⟩
    have least : ∀ ordinal, occurs ordinal →
        ∃ first, occurs first ∧ ∀ before, before < first → ¬ occurs before := by
      intro ordinal
      induction ordinal using Nat.strongRecOn with
      | ind ordinal ih =>
          intro here
          by_cases earlier : ∃ before, before < ordinal ∧ occurs before
          · obtain ⟨before, smaller, occurrence⟩ := earlier
            exact ih before smaller occurrence
          · refine ⟨ordinal, here, ?_⟩
            intro before smaller occurrence
            exact earlier ⟨before, smaller, occurrence⟩
    obtain ⟨witness, occurrence⟩ := existsOccurrence
    obtain ⟨first, firstOccurrence, minimal⟩ := least witness occurrence
    obtain ⟨index, level, atOrdinal, inside, value⟩ := firstOccurrence
    have claimed := List.fst_mem_of_mem_zipIdx atOrdinal
    apply (mem_helperCandidates_iff indices node).mpr
    refine ⟨index, first, level, atOrdinal, inside, ?_, value⟩
    apply (isHelper_iff indices index first level physical
      (physical index claimed) inside).mpr
    intro other ordinal otherMember deep
    have shiftedInside : depth other - (depth index - level) < depth other := by omega
    constructor
    · intro same
      apply missing
      apply (mem_claimPaths_iff indices node).mpr
      exact ⟨other, ordinal, depth other - (depth index - level), otherMember,
        shiftedInside, same.symm.trans value⟩
    · intro earlier same
      have occurrence : occurs ordinal := by
        refine ⟨other, depth other - (depth index - level), otherMember, shiftedInside, ?_⟩
        exact (congrArg Ssz.gindexSibling same.symm).trans value
      exact minimal ordinal earlier occurrence

end SszNative.Indices

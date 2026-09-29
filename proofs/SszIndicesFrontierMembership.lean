import SszIndicesFrontierUniqueKeys

set_option autoImplicit false

namespace SszNative.Indices

theorem isHelper_iff (indices : List NatOperand) (index : NatOperand)
    (claim level : Nat)
    (physical : ∀ other ∈ indices, other.words.length < 2^64)
    (indexPhysical : index.words.length < 2^64)
    (inside : level < depth index) :
    isHelper indices index claim level = true ↔
      ∀ other ordinal, (other, ordinal) ∈ indices.zipIdx →
        depth index - level ≤ depth other →
        Ssz.gindexSibling (index.value >>> level) ≠
          other.value >>> (depth other - (depth index - level)) ∧
        (ordinal < claim → index.value >>> level ≠
          other.value >>> (depth other - (depth index - level))) := by
  have compare (other : NatOperand) (ordinal : Nat)
      (member : (other, ordinal) ∈ indices.zipIdx) :
      (depth other >= depth index - level &&
        (prefixEqual index level true other (depth other - (depth index - level)) ||
          (ordinal < claim && prefixEqual index level false other
            (depth other - (depth index - level))))) = false ↔
        depth index - level ≤ depth other →
        Ssz.gindexSibling (index.value >>> level) ≠
          other.value >>> (depth other - (depth index - level)) ∧
        (ordinal < claim → index.value >>> level ≠
          other.value >>> (depth other - (depth index - level))) := by
    have otherPhysical := physical other (List.fst_mem_of_mem_zipIdx member)
    rw [prefixEqual_refines index level true other _ indexPhysical otherPhysical
      (candidate_flip_domain index level inside),
      prefixEqual_refines index level false other _ indexPhysical otherPhysical
        (by intro impossible; cases impossible)]
    simp [Ssz.gindexSibling]
  simp only [isHelper, Bool.not_eq_true', List.any_eq_false, Bool.not_eq_true, Prod.forall]
  exact forall_congr' fun other => forall_congr' fun ordinal =>
    forall_congr' fun member => compare other ordinal member

theorem mem_claimPaths_iff (indices : List NatOperand) (node : Nat) :
    node ∈ claimPaths (indices.map NatOperand.value) ↔
      ∃ index ordinal level, (index, ordinal) ∈ indices.zipIdx ∧
        level < depth index ∧ index.value >>> level = node := by
  have indexed (index : NatOperand) :
      index ∈ indices ↔ ∃ ordinal, (index, ordinal) ∈ indices.zipIdx := by
    constructor
    · intro member
      obtain ⟨ordinal, atOrdinal⟩ := List.mem_iff_getElem?.mp member
      exact ⟨ordinal, List.mk_mem_zipIdx_iff_getElem?.mpr atOrdinal⟩
    · rintro ⟨ordinal, member⟩
      exact List.fst_mem_of_mem_zipIdx member
  simp only [claimPaths, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨value, ⟨index, member, rfl⟩, level, inside, same⟩
    obtain ⟨ordinal, atOrdinal⟩ := (indexed index).mp member
    exact ⟨index, ordinal, level, atOrdinal, by simpa only [depth_value] using inside, same⟩
  · rintro ⟨index, ordinal, level, member, inside, same⟩
    exact ⟨index.value, ⟨index, (indexed index).mpr ⟨ordinal, member⟩, rfl⟩,
      level, by simpa only [depth_value] using inside, same⟩

theorem mem_helperCandidates_iff (indices : List NatOperand) (node : Nat) :
    node ∈ helperCandidates indices ↔
      ∃ index ordinal level, (index, ordinal) ∈ indices.zipIdx ∧
        level < depth index ∧ isHelper indices index ordinal level = true ∧
        Ssz.gindexSibling (index.value >>> level) = node := by
  constructor
  · intro member
    obtain ⟨⟨index, ordinal, level⟩, retained, value⟩ :=
      List.mem_map.mp member
    obtain ⟨present, inside, accepted⟩ :=
      (helperCandidateKeys_mem indices index ordinal level).mp retained
    exact ⟨index, ordinal, level, present, inside, accepted, value⟩
  · rintro ⟨index, ordinal, level, present, inside, accepted, value⟩
    apply List.mem_map.mpr
    exact ⟨(index, ordinal, level),
      (helperCandidateKeys_mem indices index ordinal level).mpr
        ⟨present, inside, accepted⟩, value⟩

end SszNative.Indices

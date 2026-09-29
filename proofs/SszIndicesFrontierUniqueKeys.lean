import SszIndicesFrontierCandidates

set_option autoImplicit false

namespace SszNative.Indices

/-- A retained proof key records an actual request position and one accepted
level of that request's source enumeration. -/
theorem helperCandidateKeys_mem (indices : List NatOperand) (index : NatOperand)
    (claim level : Nat) :
    (index, claim, level) ∈ helperCandidateKeys indices ↔
      (index, claim) ∈ indices.zipIdx ∧ level < depth index ∧
        isHelper indices index claim level = true := by
  unfold helperCandidateKeys
  constructor
  · intro member
    obtain ⟨⟨other, ordinal⟩, present, selected⟩ := List.mem_flatMap.mp member
    obtain ⟨candidate, retained, same⟩ := List.mem_map.mp selected
    have fields : other = index ∧ ordinal = claim ∧ candidate = level := by
      simpa only [Prod.mk.injEq] using same
    rcases fields with ⟨rfl, rfl, rfl⟩
    obtain ⟨inside, accepted⟩ := List.mem_filter.mp retained
    exact ⟨present, List.mem_range.mp inside, accepted⟩
  · rintro ⟨present, inside, accepted⟩
    exact List.mem_flatMap.mpr ⟨(index, claim), present,
      List.mem_map.mpr ⟨level,
        List.mem_filter.mpr ⟨List.mem_range.mpr inside, accepted⟩, rfl⟩⟩

/-- Positions distinguish different claims even when their raw operands are
identical; the inner range visits each level only once. -/
theorem helperCandidateKeys_nodup (indices : List NatOperand) :
    (helperCandidateKeys indices).Nodup := by
  have positions : indices.zipIdx.Pairwise (fun left right => left.2 < right.2) := by
    apply List.pairwise_iff_getElem.mpr
    intro left right leftInside rightInside before
    simpa only [List.getElem_zipIdx, Nat.zero_add] using before
  change List.Pairwise (fun left right => left ≠ right) _
  unfold helperCandidateKeys
  apply List.pairwise_flatMap.mpr
  constructor
  · intro pair _
    apply List.pairwise_map.mpr
    have levels : ((List.range (depth pair.1)).filter
        (isHelper indices pair.1 pair.2)).Pairwise (fun left right => left ≠ right) :=
      List.Pairwise.filter _ List.nodup_range
    apply levels.imp
    intro left right different same
    exact different (congrArg (fun key : NatOperand × Nat × Nat => key.2.2) same)
  · apply positions.imp
    intro left right before first firstMember second secondMember same
    obtain ⟨leftLevel, _, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨rightLevel, _, rfl⟩ := List.mem_map.mp secondMember
    have sameClaim := congrArg (fun key : NatOperand × Nat × Nat => key.2.1) same
    exact (Nat.ne_of_lt before) sameClaim

end SszNative.Indices

import SszIndicesFrontierUniqueKeys
import SszIndicesFrontierMembership

set_option autoImplicit false

namespace SszNative.Indices

/-- Equal retained siblings have equal source keys. At different request
positions the later claim's unflipped-prefix exclusion rejects the duplicate;
at the same position strict path depths determine the unique level. -/
theorem helperCandidateValue_injective (indices : List NatOperand)
    (physical : ∀ index ∈ indices, index.words.length < 2^64)
    (valid : ∀ index ∈ indices, 2 ≤ index.value)
    (left right : NatOperand × Nat × Nat)
    (leftMember : left ∈ helperCandidateKeys indices)
    (rightMember : right ∈ helperCandidateKeys indices)
    (same : helperCandidateValue left = helperCandidateValue right) :
    left = right := by
  rcases left with ⟨left, leftClaim, leftLevel⟩
  rcases right with ⟨right, rightClaim, rightLevel⟩
  obtain ⟨leftPosition, leftInside, leftAccepted⟩ :=
    (helperCandidateKeys_mem indices left leftClaim leftLevel).mp leftMember
  obtain ⟨rightPosition, rightInside, rightAccepted⟩ :=
    (helperCandidateKeys_mem indices right rightClaim rightLevel).mp rightMember
  have leftPresent : left ∈ indices := List.fst_mem_of_mem_zipIdx leftPosition
  have rightPresent : right ∈ indices := List.fst_mem_of_mem_zipIdx rightPosition
  have leftValid := valid left leftPresent
  have rightValid := valid right rightPresent
  have leftWithin : leftLevel < left.value.log2 := by
    simpa only [depth_value] using leftInside
  have rightWithin : rightLevel < right.value.log2 := by
    simpa only [depth_value] using rightInside
  have samePrefix : left.value >>> leftLevel = right.value >>> rightLevel :=
    sibling_injective _ _ same
  have leftDepth := shift_log2 left.value leftLevel (by omega) (by omega)
  have rightDepth := shift_log2 right.value rightLevel (by omega) (by omega)
  have sameDepth : depth left - leftLevel = depth right - rightLevel := by
    rw [depth_value, depth_value]
    have measured := congrArg Nat.log2 samePrefix
    omega
  have notLeftEarlier : ¬ leftClaim < rightClaim := by
    intro before
    have eligible : depth right - rightLevel ≤ depth left := by omega
    have excluded := ((isHelper_iff indices right rightClaim rightLevel physical
      (physical right rightPresent) rightInside).mp rightAccepted
        left leftClaim leftPosition eligible).2 before
    have distance : depth left - (depth right - rightLevel) = leftLevel := by omega
    rw [distance] at excluded
    exact excluded samePrefix.symm
  have notRightEarlier : ¬ rightClaim < leftClaim := by
    intro before
    have eligible : depth left - leftLevel ≤ depth right := by omega
    have excluded := ((isHelper_iff indices left leftClaim leftLevel physical
      (physical left leftPresent) leftInside).mp leftAccepted
        right rightClaim rightPosition eligible).2 before
    have distance : depth right - (depth left - leftLevel) = rightLevel := by omega
    rw [distance] at excluded
    exact excluded samePrefix
  have sameClaim : leftClaim = rightClaim := by omega
  have leftAt := List.mk_mem_zipIdx_iff_getElem?.mp leftPosition
  have rightAt := List.mk_mem_zipIdx_iff_getElem?.mp rightPosition
  rw [sameClaim] at leftAt
  have sameIndex : left = right := Option.some.inj (leftAt.symm.trans rightAt)
  subst right
  have sameLevel := path_level_unique left.value leftLevel rightLevel
    (by omega) leftWithin rightWithin samePrefix
  cases sameClaim
  cases sameLevel
  rfl

/-- The actual count/fill candidate enumeration is duplicate-free by numeric
value. No antichain, canonical representation, or output uniqueness premise is
needed: the source's earlier-claim exclusion supplies the cross-claim proof. -/
theorem helperCandidates_nodup (indices : List NatOperand)
    (physical : ∀ index ∈ indices, index.words.length < 2^64)
    (valid : ∀ index ∈ indices, 2 ≤ index.value) :
    (helperCandidates indices).Nodup := by
  change List.Pairwise (fun left right => left ≠ right)
    ((helperCandidateKeys indices).map helperCandidateValue)
  apply List.pairwise_map.mpr
  apply (helperCandidateKeys_nodup indices).imp_of_mem
  intro left right leftMember rightMember different same
  exact different (helperCandidateValue_injective indices physical valid
    left right leftMember rightMember same)

end SszNative.Indices

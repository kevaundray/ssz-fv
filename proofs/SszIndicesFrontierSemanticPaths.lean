import SszIndicesFrontierSemanticCore
import SszIndicesFrontierCandidates

set_option autoImplicit false

namespace SszNative.Indices

/-- Every proper non-root ancestor has one uniquely determined shift distance. -/
theorem strict_path_member_iff (claim ancestor : Nat) (valid : 2 ≤ claim) :
    ancestor ∈ ((List.range claim.log2).map (fun level => claim >>> level)).drop 1 ↔
      0 < ancestor.log2 ∧ ancestor.log2 < claim.log2 ∧
        claim >>> (claim.log2 - ancestor.log2) = ancestor := by
  rw [← List.map_drop]
  constructor
  · intro member
    obtain ⟨level, member, same⟩ := List.mem_map.mp member
    obtain ⟨offset, bound, selected⟩ := List.mem_drop_iff_getElem.mp member
    have selected' : 1 + offset = level := by simpa only [List.getElem_range] using selected
    simp only [List.length_range] at bound
    have positive : 0 < level := by omega
    have inside : level < claim.log2 := by omega
    have depthEq := shift_log2 claim level (by omega) (by omega)
    rw [same] at depthEq
    refine ⟨by omega, by omega, ?_⟩
    have distance : claim.log2 - ancestor.log2 = level := by omega
    simpa [distance] using same
  · rintro ⟨positive, shallower, same⟩
    apply List.mem_map.mpr
    refine ⟨claim.log2 - ancestor.log2, ?_, same⟩
    apply List.mem_drop_iff_getElem.mpr
    refine ⟨claim.log2 - ancestor.log2 - 1, ?_, ?_⟩
    · simp only [List.length_range]
      omega
    · simp only [List.getElem_range]
      omega

/-- The source's borrowed ancestor test is exactly strict path membership. -/
theorem ancestor_test_iff (claim ancestor : NatOperand) (count : Nat)
    (measured : length claim = .ok count)
    (claimPhysical : claim.words.length < 2^64)
    (ancestorPhysical : ancestor.words.length < 2^64) :
    (depth ancestor != 0 && depth ancestor < count &&
      prefixEqual claim (count - depth ancestor) false ancestor 0) = true ↔
    ancestor.value ∈ ((List.range count).map (fun level => claim.value >>> level)).drop 1 := by
  obtain ⟨countEq, positive, valid⟩ := length_success claim count measured
  rw [prefixEqual_refines claim (count - depth ancestor) false ancestor 0
    claimPhysical ancestorPhysical (by intro impossible; contradiction)]
  simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.false_eq_true,
    ↓reduceIte, Nat.xor_zero, Nat.shiftRight_zero]
  rw [countEq, depth_value, depth_value, strict_path_member_iff claim.value ancestor.value valid]
  omega

end SszNative.Indices

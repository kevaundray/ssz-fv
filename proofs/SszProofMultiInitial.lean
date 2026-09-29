import SszProofMultiView
import SszProofMultiStableRoot
import SszIndicesPinnedAntichain

set_option autoImplicit false

namespace SszNative.Proof

private theorem zip_keys (indices : List Nat) (values : List Ssz.Bytes)
    (same : values.length = indices.length) :
    (indices.zip values).map Prod.fst = indices := by
  induction indices generalizing values with
  | nil => cases values <;> simp_all
  | cons index rest ih =>
      cases values with
      | nil => simp at same
      | cons value tail =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at same
          simp [ih tail same]

theorem multiInitialNodes_keys (leaves proof : List Ssz.Bytes)
    (indices helpers : List NatOperand) (hl : leaves.length = indices.length)
    (hp : proof.length = helpers.length) :
    ((multiInitialNodes leaves proof indices helpers hl hp).map
      (MultiNode.erase leaves proof rfl rfl)).map Prod.fst =
      indices.map NatOperand.value ++ helpers.map NatOperand.value := by
  rw [multiInitialNodes_erase, List.map_append,
    zip_keys _ _ (by simpa using hl), zip_keys _ _ (by simpa using hp)]

theorem multiInitialNodes_unique (leaves proof : List Ssz.Bytes)
    (indices helpers : List NatOperand) (hl : leaves.length = indices.length)
    (hp : proof.length = helpers.length)
    (built : Ssz.getHelperIndices (indices.map NatOperand.value) =
      .ok (helpers.map NatOperand.value)) :
    (((multiInitialNodes leaves proof indices helpers hl hp).map
      (MultiNode.erase leaves proof rfl rfl)).map Prod.fst).Nodup := by
  rw [multiInitialNodes_keys]
  exact Indices.pinned_helper_all_nodup built

theorem multiInitialNodes_antichain (leaves proof : List Ssz.Bytes)
    (indices helpers : List NatOperand) (hl : leaves.length = indices.length)
    (hp : proof.length = helpers.length)
    (built : Ssz.getHelperIndices (indices.map NatOperand.value) =
      .ok (helpers.map NatOperand.value)) :
    Pure.ProofAntichain ((multiInitialNodes leaves proof indices helpers hl hp).map
      (MultiNode.erase leaves proof rfl rfl)) := by
  intro i im j jm step same
  rw [multiInitialNodes_keys] at im jm
  exact Indices.pinned_helper_antichain built i im j jm step same

private theorem initial_valid {l p : Nat} (index : NatOperand) (value : MultiValue l p)
    (physical : index.words.length < 2^64) (nonroot : 2 ≤ index.value) :
    (MultiNode.mk index 0 (Indices.depth index) value).Valid := by
  refine ⟨physical, ?_, ?_, ?_, ?_⟩
  · simp only [MultiNode.position, Nat.shiftRight_zero]
    omega
  · simp [MultiNode.position, Ssz.levelOf, Indices.depth_value]
  · simp
  · cases value <;> simp [nonroot]

theorem multiInitialNodes_valid (leaves proof : List Ssz.Bytes)
    (indices helpers : List NatOperand) (hl : leaves.length = indices.length)
    (hp : proof.length = helpers.length)
    (physical : ∀ index ∈ indices ++ helpers, index.words.length < 2^64)
    (nonroot : ∀ index ∈ indices ++ helpers, 2 ≤ index.value) :
    ∀ node ∈ multiInitialNodes leaves proof indices helpers hl hp, node.Valid := by
  intro node member
  simp only [multiInitialNodes, List.mem_append, List.mem_ofFn] at member
  rcases member with ⟨position, rfl⟩ | ⟨position, rfl⟩
  · have member : indices[position] ∈ indices ++ helpers :=
      List.mem_append.mpr (.inl (List.getElem_mem position.isLt))
    exact initial_valid _ _ (physical _ member) (nonroot _ member)
  · have member : helpers[position] ∈ indices ++ helpers :=
      List.mem_append.mpr (.inr (List.getElem_mem position.isLt))
    exact initial_valid _ _ (physical _ member) (nonroot _ member)

theorem multiInitialIndices_nonroot (indices helpers : List NatOperand)
    (built : Ssz.getHelperIndices (indices.map NatOperand.value) =
      .ok (helpers.map NatOperand.value)) :
    ∀ index ∈ indices ++ helpers, 2 ≤ index.value := by
  intro index member
  rcases List.mem_append.mp member with claim | helper
  · exact (Indices.pinned_helper_info built).2.1 _ (List.mem_map.mpr ⟨index, claim, rfl⟩)
  · exact (Indices.pinned_helper_sibling built
      (Or.inr (List.mem_map.mpr ⟨index, helper, rfl⟩))).1

theorem multiDepths_erase {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (nodes : List (MultiNode l p))
    (valid : ∀ node ∈ nodes, node.Valid) :
    nodes.map MultiNode.depth =
      (nodes.map (MultiNode.erase leaves proof hl hp)).map (fun pair => Ssz.levelOf pair.1) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro node member
  exact (valid node member).depth_eq

end SszNative.Proof

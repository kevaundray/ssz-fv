import SszProofMultiReservedRefinement
import SszProofMultiHelperResources
import SszProofIndicesRefinement
import SszProofRefinement
import SszIndicesFrontierSemanticBuild

set_option autoImplicit false

namespace SszNative.Proof

/-- Composition at the completed child-call boundary. The public theorem
supplies the index provider's total law; no future fold/root is hypothesized. -/
theorem multiEndpoint_refines (leaves proof : List Ssz.Bytes) (indices : List NatOperand)
    (nodeLayout : TypedArena.Layout) (arena : Delimited.ArenaState)
    (leafPhysical : leaves.length < 2^64) (proofPhysical : proof.length < 2^64)
    (indicesPhysical : indices.length < 2^64)
    (wordsPhysical : ∀ index ∈ indices, index.words.length < 2^64)
    (helpersRefined :
      Indices.eraseResult ((Indices.helperIndices indices arena.base arena.capacity arena.used).result.map
        (fun helpers => helpers.values.map NatOperand.value)) =
        .ok (Ssz.getHelperIndices (indices.map NatOperand.value)) ∨
      (Indices.helperIndices indices arena.base arena.capacity arena.used).result =
        .error Indices.scratch) :
    Refines Eq (calculateMultiMerkleRoot leaves proof indices nodeLayout arena)
      (Ssz.calculateMultiMerkleRoot leaves proof (indices.map NatOperand.value)) := by
  have wide : 2^64 < 2^128 := by decide
  by_cases leafCount : leaves.length = indices.length
  · have first := liftIndices_frontier_refines arena
      (Indices.helperIndices indices arena.base arena.capacity arena.used)
      (Ssz.getHelperIndices (indices.map NatOperand.value)) helpersRefined
    simp only [calculateMultiMerkleRoot, leafCount, ↓reduceDIte,
      Ssz.calculateMultiMerkleRoot, List.length_map, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind, Pure.pure, Except.pure]
    apply ResultRefines.bind_success
      (fun (helpers : Indices.NatSlice) (values : List Nat) =>
        helpers.values.map NatOperand.value = values) Eq _ _ _ _ first
    intro helpers values completed same used
    have helperSuccess : (Indices.helperIndices indices arena.base arena.capacity arena.used).result =
        .ok helpers := by
      cases result : (Indices.helperIndices indices arena.base arena.capacity arena.used).result <;>
        simp_all [liftIndices]
    have built : Ssz.getHelperIndices (indices.map NatOperand.value) =
        .ok (helpers.values.map NatOperand.value) := by
      rcases helpersRefined with semantic | exhausted
      · simpa [helperSuccess, Indices.eraseResult] using semantic.symm
      · rw [helperSuccess] at exhausted
        contradiction
    subst values
    have helperPhysical := Indices.helperIndices_success_physical indices arena.base arena.capacity
      arena.used helpers helperSuccess
    have helperCountPhysical := multiHelper_count_physical indices arena helpers helperSuccess
    by_cases proofCount : proof.length = helpers.values.length
    · have allPhysical : ∀ index ∈ indices ++ helpers.values, index.words.length < 2^64 := by
        intro index member
        exact (List.mem_append.mp member).elim (wordsPhysical index) (helperPhysical index)
      simpa only [proofCount, ↓reduceDIte, List.length_map, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind, Pure.pure, Except.pure]
        using multiReserved_refines leaves proof indices helpers.values leafCount proofCount nodeLayout
          { arena with used := used } allPhysical built
    · have different : (proof.length != helpers.values.length) = true := by simp [proofCount]
      simpa only [proofCount, ↓reduceDIte, List.length_map, different, ↓reduceIte,
        Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw, CountReason.erase]
        using failCount_refines (α := Ssz.Bytes) .proofLength helpers.values.length proof.length
          { arena with used := used } (Nat.lt_trans helperCountPhysical wide)
          (Nat.lt_trans proofPhysical wide)
  · have different : (leaves.length != indices.length) = true := by simp [leafCount]
    simpa only [calculateMultiMerkleRoot, leafCount, ↓reduceDIte,
      Ssz.calculateMultiMerkleRoot, List.length_map, different, ↓reduceIte,
      Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw, CountReason.erase]
      using failCount_refines (α := Ssz.Bytes) .leafCount indices.length leaves.length arena
        (Nat.lt_trans indicesPhysical wide) (Nat.lt_trans leafPhysical wide)

end SszNative.Proof

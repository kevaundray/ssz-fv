import SszProofMultiFoldRefinement

set_option autoImplicit false

namespace SszNative.Proof

/-- This internal composition begins after helper construction has completed.
The helper equation supplies input frontier facts, never future root success. -/
theorem multiReserved_refines (leaves proof : List Ssz.Bytes)
    (indices helpers : List NatOperand) (hl : leaves.length = indices.length)
    (hp : proof.length = helpers.length) (layout : TypedArena.Layout)
    (arena : Delimited.ArenaState)
    (physical : ∀ index ∈ indices ++ helpers, index.words.length < 2^64)
    (built : Ssz.getHelperIndices (indices.map NatOperand.value) =
      .ok (helpers.map NatOperand.value)) :
    Refines Eq (multiReserved leaves proof indices helpers hl hp layout arena)
      (let nodes := (indices.map NatOperand.value).zip leaves ++
        (helpers.map NatOperand.value).zip proof
       Ssz.foldToRoot ((nodes.map (fun pair => Ssz.levelOf pair.1)).foldl max 0) nodes) := by
  by_cases count : indices.length + helpers.length < 2^64
  · cases reserved : TypedArena.reserve layout arena.base arena.capacity arena.used
        (indices.length + helpers.length) with
    | none =>
        simp only [multiReserved, count, ↓reduceIte, reserved]
        exact .exhausted .scratchExhausted trivial _
    | some reservation =>
        let nodes := multiInitialNodes leaves proof indices helpers hl hp
        have valid : ∀ node ∈ nodes, node.Valid :=
          multiInitialNodes_valid leaves proof indices helpers hl hp physical
            (multiInitialIndices_nonroot indices helpers built)
        have unique := multiInitialNodes_unique leaves proof indices helpers hl hp built
        have separated := multiInitialNodes_antichain leaves proof indices helpers hl hp built
        have folded := multiFold_refines leaves proof rfl rfl
          ((nodes.map MultiNode.depth).foldl max 0) nodes valid unique separated
        have depths := congrArg (fun values : List Nat => values.foldl max 0)
          (multiDepths_erase leaves proof rfl rfl nodes valid)
        have erased := multiInitialNodes_erase leaves proof indices helpers hl hp
        change nodes.map (MultiNode.erase leaves proof rfl rfl) = _ at erased
        rw [erased] at folded depths
        rw [depths] at folded
        simpa only [multiReserved, count, ↓reduceIte, reserved, Refines, nodes] using folded
  · simp only [multiReserved, count, ↓reduceIte]
    exact .exhausted .scratchExhausted trivial _

end SszNative.Proof

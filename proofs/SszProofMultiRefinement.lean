import SszProofMultiEndpoint
import SszIndicesFrontierSemanticErrors
import SszProofMultiSize

set_option autoImplicit false

namespace SszNative.Proof

/-- Total pinned refinement for raw multiproof reconstruction. Only physical
slice/limb bounds are assumed. Raw blobs may be empty, aliased, or any width;
claims need not be readable from a schema, and no future success is assumed. -/
theorem calculateMultiMerkleRoot_refines (leaves proof : List Ssz.Bytes)
    (indices : List NatOperand) (nodeLayout : TypedArena.Layout) (arena : Delimited.ArenaState)
    (leafPhysical : leaves.length < 2^64) (proofPhysical : proof.length < 2^64)
    (indicesPhysical : indices.length < 2^64)
    (wordsPhysical : ∀ index ∈ indices, index.words.length < 2^64) :
    Refines Eq (calculateMultiMerkleRoot leaves proof indices nodeLayout arena)
      (Ssz.calculateMultiMerkleRoot leaves proof (indices.map NatOperand.value)) :=
  multiEndpoint_refines leaves proof indices nodeLayout arena leafPhysical proofPhysical
    indicesPhysical wordsPhysical
    (Indices.helperIndices_refines indices arena.base arena.capacity arena.used wordsPhysical)

theorem calculateNativeMultiMerkleRoot_refines (leaves proof : List Ssz.Bytes)
    (indices : List NatOperand) (arena : Delimited.ArenaState)
    (leafPhysical : leaves.length < 2^64) (proofPhysical : proof.length < 2^64)
    (indicesPhysical : indices.length < 2^64)
    (wordsPhysical : ∀ index ∈ indices, index.words.length < 2^64) :
    Refines Eq (calculateNativeMultiMerkleRoot leaves proof indices arena)
      (Ssz.calculateMultiMerkleRoot leaves proof (indices.map NatOperand.value)) :=
  calculateMultiMerkleRoot_refines leaves proof indices nativeNodeLayout arena
    leafPhysical proofPhysical indicesPhysical wordsPhysical

end SszNative.Proof

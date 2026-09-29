import SszProofWidthsRefinement
import SszProofMultiRefinement

set_option autoImplicit false

namespace SszNative.Proof

/-- Public width-checked multiproof refinement. All premises describe actual
physical input slices; none require a future helper/root read to succeed. -/
theorem verifyMerkleMultiproof_refines (leaves proof : List Ssz.Bytes)
    (indices : List NatOperand) (root : Ssz.Bytes) (nodeLayout : TypedArena.Layout)
    (arena : Delimited.ArenaState) (leafCountPhysical : leaves.length < 2^64)
    (proofCountPhysical : proof.length < 2^64) (indicesPhysical : indices.length < 2^64)
    (wordsPhysical : ∀ index ∈ indices, index.words.length < 2^64)
    (rootPhysical : root.size < 2^64)
    (leafPhysical : ∀ node ∈ leaves, node.size < 2^64)
    (proofPhysical : ∀ node ∈ proof, node.size < 2^64) :
    Refines Eq (verifyMerkleMultiproof leaves proof indices root nodeLayout arena)
      (Ssz.verifyMerkleMultiproof leaves proof (indices.map NatOperand.value) root) := by
  apply verifyMerkleMultiproof_of_raw_refines leaves proof indices root nodeLayout arena
    rootPhysical leafPhysical proofPhysical
  intro cursor
  exact calculateMultiMerkleRoot_refines leaves proof indices nodeLayout cursor
    leafCountPhysical proofCountPhysical indicesPhysical wordsPhysical

/-- Measured source-exact Node layout on both targets, with all variant and tail
padding left opaque. Width/order semantics do not depend on that padding. -/
def verifyNativeMerkleMultiproof (leaves proof : List Ssz.Bytes) (indices : List NatOperand)
    (root : Ssz.Bytes) (arena : Delimited.ArenaState) : Outcome Bool :=
  verifyMerkleMultiproof leaves proof indices root nativeNodeLayout arena

theorem verifyNativeMerkleMultiproof_refines (leaves proof : List Ssz.Bytes)
    (indices : List NatOperand) (root : Ssz.Bytes) (arena : Delimited.ArenaState)
    (leafCountPhysical : leaves.length < 2^64) (proofCountPhysical : proof.length < 2^64)
    (indicesPhysical : indices.length < 2^64)
    (wordsPhysical : ∀ index ∈ indices, index.words.length < 2^64)
    (rootPhysical : root.size < 2^64)
    (leafPhysical : ∀ node ∈ leaves, node.size < 2^64)
    (proofPhysical : ∀ node ∈ proof, node.size < 2^64) :
    Refines Eq (verifyNativeMerkleMultiproof leaves proof indices root arena)
      (Ssz.verifyMerkleMultiproof leaves proof (indices.map NatOperand.value) root) :=
  verifyMerkleMultiproof_refines leaves proof indices root nativeNodeLayout arena
    leafCountPhysical proofCountPhysical indicesPhysical wordsPhysical rootPhysical
    leafPhysical proofPhysical

end SszNative.Proof

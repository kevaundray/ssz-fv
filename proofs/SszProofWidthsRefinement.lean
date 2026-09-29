import SszProofWidths
import SszProofSingleRefinement

set_option autoImplicit false

namespace SszNative.Proof

theorem checkChunk_refines (node : Ssz.Bytes) (arena : Delimited.ArenaState)
    (physical : node.size < 2^128) :
    Refines Eq (checkChunk node arena) (Ssz.checkChunk node) := by
  unfold checkChunk Ssz.checkChunk
  change Refines Eq (if node.size = 32 then unchanged arena.used (.ok ())
      else failCount .count 32 node.size arena)
    (if node.size = 32 then .ok () else .error (.count 32 node.size))
  split
  · exact .ok () () rfl
  · exact failCount_refines .count 32 node.size arena (by decide) physical

theorem checkChunks_refines (nodes : List Ssz.Bytes) (arena : Delimited.ArenaState)
    (physical : ∀ node ∈ nodes, node.size < 2^128) :
    Refines Eq (checkChunks nodes arena) (Ssz.checkChunks nodes) := by
  induction nodes generalizing arena with
  | nil => exact .ok () () rfl
  | cons node rest ih =>
      simp only [checkChunks, Ssz.checkChunks]
      apply ResultRefines.bind Eq Eq _ _ _ _
        (checkChunk_refines node arena (physical node (by simp)))
      intro left right same used
      exact ih { arena with used := used } (fun value member => physical value (by simp [member]))

/-- Complete checked-single contract: malformed widths/structure are errors;
well-formed unequal roots return false, and every raw byte is compared. -/
theorem verifyMerkleProof_refines (leaf : Ssz.Bytes) (proof : List Ssz.Bytes)
    (index : NatOperand) (root : Ssz.Bytes) (arena : Delimited.ArenaState)
    (indexPhysical : index.words.length < 2^64) (proofPhysical : proof.length < 2^64)
    (leafPhysical : leaf.size < 2^64) (rootPhysical : root.size < 2^64)
    (proofBytesPhysical : ∀ node ∈ proof, node.size < 2^64) :
    Refines Eq (verifyMerkleProof leaf proof index root arena)
      (Ssz.verifyMerkleProof leaf proof index.value root) := by
  unfold verifyMerkleProof Ssz.verifyMerkleProof
  apply ResultRefines.bind Eq Eq _ _ _ _
    (checkChunk_refines leaf arena (by omega))
  intro leafCheck leafCheck' same used
  apply ResultRefines.bind Eq Eq _ _ _ _
    (checkChunk_refines root { arena with used := used } (by omega))
  intro rootCheck rootCheck' same' used'
  apply ResultRefines.bind Eq Eq _ _ _ _
    (checkChunks_refines proof { arena with used := used' }
      (fun node member => by have := proofBytesPhysical node member; omega))
  intro proofCheck proofCheck' same'' used''
  apply ResultRefines.bind Eq Eq _ _ _ _
    (calculateMerkleRoot_refines leaf proof index { arena with used := used'' }
      indexPhysical proofPhysical)
  intro actual expected equal used'''
  subst expected
  exact .ok _ _ rfl

/-- These compositional width checks require no successful future reconstruction.
The caller supplies the already-proved total raw contract for every arena cursor. -/
theorem verifyMerkleMultiproof_of_raw_refines (leaves proof : List Ssz.Bytes)
    (indices : List NatOperand) (root : Ssz.Bytes) (nodeLayout : TypedArena.Layout)
    (arena : Delimited.ArenaState) (rootPhysical : root.size < 2^64)
    (leafPhysical : ∀ node ∈ leaves, node.size < 2^64)
    (proofPhysical : ∀ node ∈ proof, node.size < 2^64)
    (raw : ∀ cursor, Refines Eq
      (calculateMultiMerkleRoot leaves proof indices nodeLayout cursor)
      (Ssz.calculateMultiMerkleRoot leaves proof (indices.map NatOperand.value))) :
    Refines Eq (verifyMerkleMultiproof leaves proof indices root nodeLayout arena)
      (Ssz.verifyMerkleMultiproof leaves proof (indices.map NatOperand.value) root) := by
  unfold verifyMerkleMultiproof Ssz.verifyMerkleMultiproof
  apply ResultRefines.bind Eq Eq _ _ _ _
    (checkChunk_refines root arena (by omega))
  intro rootCheck rootCheck' same used
  apply ResultRefines.bind Eq Eq _ _ _ _
    (checkChunks_refines leaves { arena with used := used }
      (fun node member => by have := leafPhysical node member; omega))
  intro leafCheck leafCheck' same' used'
  apply ResultRefines.bind Eq Eq _ _ _ _
    (checkChunks_refines proof { arena with used := used' }
      (fun node member => by have := proofPhysical node member; omega))
  intro proofCheck proofCheck' same'' used''
  apply ResultRefines.bind Eq Eq _ _ _ _ (raw { arena with used := used'' })
  intro actual expected equal used'''
  subst expected
  exact .ok _ _ rfl

end SszNative.Proof

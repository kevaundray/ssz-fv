import SszProofSingle
import SszProofMulti

set_option autoImplicit false

namespace SszNative.Proof

def checkChunk (node : Ssz.Bytes) (arena : Delimited.ArenaState) : Outcome Unit :=
  if node.size = 32 then unchanged arena.used (.ok ())
  else failCount .count 32 node.size arena

def checkChunks : List Ssz.Bytes → Delimited.ArenaState → Outcome Unit
  | [], arena => unchanged arena.used (.ok ())
  | node :: rest, arena =>
      bind (checkChunk node arena) fun _ used =>
        checkChunks rest { arena with used := used }

/-- Single verification checks leaf, root, then each sibling before any index
validation or reconstruction. Equality, not a collision assumption, decides. -/
def verifyMerkleProof (leaf : Ssz.Bytes) (proof : List Ssz.Bytes) (index : NatOperand)
    (root : Ssz.Bytes) (arena : Delimited.ArenaState) : Outcome Bool :=
  bind (checkChunk leaf arena) fun _ used =>
    bind (checkChunk root { arena with used := used }) fun _ used =>
      bind (checkChunks proof { arena with used := used }) fun _ used =>
        bind (calculateMerkleRoot leaf proof index { arena with used := used }) fun actual used =>
          unchanged used (.ok (actual == root))

/-- Multiproof verification instead checks root, leaves, then helpers; only
then can count, claim validation, helper allocation, or reduction occur. -/
def verifyMerkleMultiproof (leaves proof : List Ssz.Bytes) (indices : List NatOperand)
    (root : Ssz.Bytes) (nodeLayout : TypedArena.Layout) (arena : Delimited.ArenaState) :
    Outcome Bool :=
  bind (checkChunk root arena) fun _ used =>
    bind (checkChunks leaves { arena with used := used }) fun _ used =>
      bind (checkChunks proof { arena with used := used }) fun _ used =>
        bind (calculateMultiMerkleRoot leaves proof indices nodeLayout
          { arena with used := used }) fun actual used =>
            unchanged used (.ok (actual == root))

theorem checkChunk_width (node : Ssz.Bytes) (arena : Delimited.ArenaState)
    (width : node.size = 32) : checkChunk node arena = unchanged arena.used (.ok ()) := by
  simp only [checkChunk, width, ↓reduceIte]

theorem checkChunks_widths (nodes : List Ssz.Bytes) (arena : Delimited.ArenaState)
    (widths : ∀ node ∈ nodes, node.size = 32) :
    checkChunks nodes arena = unchanged arena.used (.ok ()) := by
  induction nodes generalizing arena with
  | nil => rfl
  | cons node rest ih =>
      simp only [checkChunks, checkChunk_width node arena (widths node (by simp)), bind_unchanged]
      exact ih arena (fun node member => widths node (by simp [member]))

theorem verifyMerkleProof_widths (leaf : Ssz.Bytes) (proof : List Ssz.Bytes)
    (index : NatOperand) (root : Ssz.Bytes) (arena : Delimited.ArenaState)
    (leafWidth : leaf.size = 32) (rootWidth : root.size = 32)
    (proofWidths : ∀ node ∈ proof, node.size = 32) :
    verifyMerkleProof leaf proof index root arena =
      bind (calculateMerkleRoot leaf proof index arena) fun actual used =>
        unchanged used (.ok (actual == root)) := by
  simp only [verifyMerkleProof, checkChunk_width leaf arena leafWidth, bind_unchanged,
    checkChunk_width root arena rootWidth, checkChunks_widths proof arena proofWidths]

theorem verifyMerkleMultiproof_widths (leaves proof : List Ssz.Bytes)
    (indices : List NatOperand) (root : Ssz.Bytes) (nodeLayout : TypedArena.Layout)
    (arena : Delimited.ArenaState) (rootWidth : root.size = 32)
    (leafWidths : ∀ node ∈ leaves, node.size = 32)
    (proofWidths : ∀ node ∈ proof, node.size = 32) :
    verifyMerkleMultiproof leaves proof indices root nodeLayout arena =
      bind (calculateMultiMerkleRoot leaves proof indices nodeLayout arena) fun actual used =>
        unchanged used (.ok (actual == root)) := by
  simp only [verifyMerkleMultiproof, checkChunk_width root arena rootWidth, bind_unchanged,
    checkChunks_widths leaves arena leafWidths, checkChunks_widths proof arena proofWidths]

theorem verifyMerkleProof_leaf_error (leaf : Ssz.Bytes) (proof : List Ssz.Bytes)
    (index : NatOperand) (root : Ssz.Bytes) (arena : Delimited.ArenaState) (reason : Error)
    (failed : (checkChunk leaf arena).result = .error reason) :
    verifyMerkleProof leaf proof index root arena =
      ⟨.error reason, (checkChunk leaf arena).used, (checkChunk leaf arena).effects⟩ := by
  simp only [verifyMerkleProof, bind, failed]

theorem verifyMerkleMultiproof_root_error (leaves proof : List Ssz.Bytes)
    (indices : List NatOperand) (root : Ssz.Bytes) (nodeLayout : TypedArena.Layout)
    (arena : Delimited.ArenaState) (reason : Error)
    (failed : (checkChunk root arena).result = .error reason) :
    verifyMerkleMultiproof leaves proof indices root nodeLayout arena =
      ⟨.error reason, (checkChunk root arena).used, (checkChunk root arena).effects⟩ := by
  simp only [verifyMerkleMultiproof, bind, failed]

/-- Different raw operand boundaries are intentionally indistinguishable to
raw hashing whenever concatenation is equal. Width checks remain separate. -/
theorem rawCombine_same_concatenation (left right left' right' : Ssz.Bytes)
    (same : left ++ right = left' ++ right') : rawCombine left right = rawCombine left' right' := by
  simp only [rawCombine_eq, Ssz.combine, same]

end SszNative.Proof

import SszProofTypes
import SszIndicesCore

set_option autoImplicit false

namespace SszNative.Proof

/-- Later branch levels consume a previously computed digest. The first level
is separate below because the input leaf is an arbitrary borrowed byte blob. -/
def climb (index : NatOperand) : Nat → Ssz.Bytes → List Ssz.Bytes → Ssz.Bytes
  | _, node, [] => node
  | level, node, sibling :: rest =>
      let parent := if Indices.bit index level then rawCombine sibling node
        else rawCombine node sibling
      climb index (level + 1) parent rest

/-- Source length validation precedes count-error metadata allocation. No input
blob is padded, truncated, copied into scratch, or assumed disjoint. -/
def calculateMerkleRoot (leaf : Ssz.Bytes) (proof : List Ssz.Bytes)
    (index : NatOperand) (arena : Delimited.ArenaState) : Outcome Ssz.Bytes :=
  match Indices.length index with
  | .error reason => unchanged arena.used (.error (.indices reason))
  | .ok depth =>
      if proof.length != depth then failCount .branchLength depth proof.length arena
      else match proof with
      | [] => unchanged arena.used (.error .proofIncomplete)
      | sibling :: rest =>
          let node := if Indices.bit index 0 then rawCombine sibling leaf
            else rawCombine leaf sibling
          unchanged arena.used (.ok (climb index 1 node rest))

theorem climb_size (index : NatOperand) (level : Nat) (node : Ssz.Bytes)
    (proof : List Ssz.Bytes) (sized : node.size = 32) :
    (climb index level node proof).size = 32 := by
  induction proof generalizing level node with
  | nil => exact sized
  | cons sibling rest ih =>
      simp only [climb]
      apply ih
      split <;> exact rawCombine_size _ _

theorem calculateMerkleRoot_length_error (leaf : Ssz.Bytes) (proof : List Ssz.Bytes)
    (index : NatOperand) (arena : Delimited.ArenaState) (reason : Indices.Error)
    (failed : Indices.length index = .error reason) :
    calculateMerkleRoot leaf proof index arena = unchanged arena.used (.error (.indices reason)) := by
  simp only [calculateMerkleRoot, failed]

theorem calculateMerkleRoot_success_size (leaf : Ssz.Bytes) (proof : List Ssz.Bytes)
    (index : NatOperand) (arena : Delimited.ArenaState) (root : Ssz.Bytes)
    (success : (calculateMerkleRoot leaf proof index arena).result = .ok root) :
    root.size = 32 := by
  unfold calculateMerkleRoot at success
  split at success
  · cases success
  · split at success
    · unfold failCount bind at success
      split at success <;> cases success
    · split at success
      · cases success
      · cases success
        apply climb_size
        split <;> exact rawCombine_size _ _

/-- The only success branch is allocation-free: counts allocate only on error. -/
theorem calculateMerkleRoot_success_resources (leaf : Ssz.Bytes) (proof : List Ssz.Bytes)
    (index : NatOperand) (arena : Delimited.ArenaState) (root : Ssz.Bytes)
    (success : (calculateMerkleRoot leaf proof index arena).result = .ok root) :
    (calculateMerkleRoot leaf proof index arena).used = arena.used ∧
      (calculateMerkleRoot leaf proof index arena).effects = [] := by
  cases checked : Indices.length index with
  | error reason =>
      simp only [calculateMerkleRoot, checked, unchanged] at success
      cases success
  | ok depth =>
      by_cases wrong : proof.length != depth
      · simp only [calculateMerkleRoot, checked, wrong, ↓reduceIte] at success
        unfold failCount bind at success
        split at success <;> cases success
      · cases proof with
        | nil =>
            simp only [calculateMerkleRoot, checked, wrong, unchanged] at success
            cases success
        | cons sibling rest =>
            simpa only [calculateMerkleRoot, checked, wrong, Bool.false_eq_true, ↓reduceIte, unchanged] using
              (show arena.used = arena.used ∧ ([] : List Effect) = [] from ⟨rfl, rfl⟩)

end SszNative.Proof

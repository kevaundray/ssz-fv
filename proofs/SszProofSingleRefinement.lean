import SszProofSingle
import SszProofRefinement
import SszIndicesArithmeticSemanticCore

set_option autoImplicit false

namespace SszNative.Proof

theorem climb_refines (index : NatOperand) (level : Nat) (node : Ssz.Bytes)
    (proof : List Ssz.Bytes) (physical : index.words.length < 2^64) :
    climb index level node proof = Ssz.climbBranch index.value level node proof := by
  induction proof generalizing level node with
  | nil => rfl
  | cons sibling rest ih =>
      simp only [climb, Ssz.climbBranch, Indices.bit_refines index level physical,
        rawCombine_eq]
      exact ih (level + 1) _

theorem indicesResult_refines {α : Type} (actual : Except Indices.Error α)
    (expected : Except Ssz.Err α) (same : Indices.eraseResult actual = .ok expected) :
    ResultRefines Eq (actual.mapError Error.indices) expected := by
  cases actual with
  | ok value =>
      simp only [Indices.eraseResult, Except.ok.injEq] at same
      subst expected
      exact .ok value value rfl
  | error reason =>
      cases expected with
      | ok value => cases reason <;> cases same
      | error fault =>
          apply ResultRefines.error (.indices reason) fault
          cases reason <;> simp_all [eraseResult, Indices.eraseResult]

theorem length_success_properties (index : NatOperand) (depth : Nat)
    (physical : index.words.length < 2^64) (success : Indices.length index = .ok depth) :
    0 < depth ∧ depth < 2^128 := by
  have bound := Indices.bitLength_u128 index physical
  unfold Indices.length Indices.checkedDepth at success
  split at success
  · cases success
  · simp only [Bind.bind, Except.bind] at success
    split at success
    · cases success
    · cases success
      simp only [Indices.depth] at *
      omega

theorem calculateMerkleRoot_bind (leaf : Ssz.Bytes) (proof : List Ssz.Bytes)
    (index : NatOperand) (arena : Delimited.ArenaState) :
    calculateMerkleRoot leaf proof index arena =
      bind (unchanged arena.used ((Indices.length index).mapError Error.indices)) fun depth used =>
        if proof.length != depth then
          failCount .branchLength depth proof.length { arena with used := used }
        else match proof with
        | [] => unchanged used (.error .proofIncomplete)
        | sibling :: rest =>
            unchanged used (.ok (climb index 1
              (if Indices.bit index 0 then rawCombine sibling leaf else rawCombine leaf sibling)
              rest)) := by
  cases checked : Indices.length index with
  | error reason =>
      simp only [calculateMerkleRoot, checked, Except.mapError, unchanged, bind]
  | ok depth =>
      simp only [calculateMerkleRoot, checked, Except.mapError, unchanged, bind, List.nil_append]
      split
      · rfl
      · cases proof <;> rfl

theorem calculateMerkleRoot_refines (leaf : Ssz.Bytes) (proof : List Ssz.Bytes)
    (index : NatOperand) (arena : Delimited.ArenaState)
    (physical : index.words.length < 2^64) (proofPhysical : proof.length < 2^64) :
    Refines Eq (calculateMerkleRoot leaf proof index arena)
      (Ssz.calculateMerkleRoot leaf proof index.value) := by
  rw [calculateMerkleRoot_bind]
  unfold Ssz.calculateMerkleRoot
  apply ResultRefines.bind_success Eq Eq _ _ _ _
    (indicesResult_refines (Indices.length index) _ (Indices.length_erase index))
  intro depth expected checked same used
  subst expected
  have lengthEq : Indices.length index = .ok depth := by
    cases resultEq : Indices.length index <;>
      simp only [unchanged, resultEq, Except.mapError, Except.ok.injEq] at checked
    · cases checked
    · subst depth
      rfl
  obtain ⟨positive, bounded⟩ := length_success_properties index depth physical lengthEq
  by_cases wrong : proof.length != depth
  · simp only [wrong, ↓reduceIte]
    exact failCount_refines .branchLength depth proof.length { arena with used := used }
      bounded (by omega)
  · simp only [wrong, Bool.false_eq_true, ↓reduceIte]
    cases proof with
    | nil => simp at wrong; omega
    | cons sibling rest =>
        apply ResultRefines.ok _ _
        simp only [Ssz.climbBranch, climb_refines index 1 _ rest physical,
          Indices.bit_refines index 0 physical, rawCombine_eq]

end SszNative.Proof

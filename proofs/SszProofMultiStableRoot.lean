import SszProofMultiStable
import SszProofMultiPermutation

set_option autoImplicit false

namespace SszNative.Proof

def stableFoldToRoot : Nat → List (Nat × Ssz.Bytes) → Except Ssz.Err Ssz.Bytes
  | 0, nodes =>
      match Ssz.nodeAt nodes 1 with
      | some root => .ok root
      | none => .error .proofIncomplete
  | depth + 1, nodes => do stableFoldToRoot depth (← stableFoldLevel (depth + 1) nodes)

theorem stableFoldLevel_complete {depth : Nat} {nodes pinned : List (Nat × Ssz.Bytes)}
    (success : Ssz.foldLevel depth nodes = .ok pinned) :
    ∃ stable, stableFoldLevel depth nodes = .ok stable ∧ stable.Perm pinned := by
  cases step : stableFoldLevel depth nodes with
  | error reason =>
      have failed := stableFoldLevel_error step
      rw [success] at failed
      contradiction
  | ok stable =>
      obtain ⟨result, built, perm⟩ := stableFoldLevel_success step
      rw [success] at built
      cases built
      exact ⟨stable, rfl, perm⟩

/-- Stable compaction and parents-first compaction have identical success sets,
even for arbitrary malformed frontiers. -/
theorem stableFoldToRoot_success_iff (depth : Nat) (nodes : List (Nat × Ssz.Bytes)) :
    (∃ root, stableFoldToRoot depth nodes = .ok root) ↔
      (∃ root, Ssz.foldToRoot depth nodes = .ok root) := by
  induction depth generalizing nodes with
  | zero => rfl
  | succ depth ih =>
      cases step : stableFoldLevel (depth + 1) nodes with
      | error reason =>
          have failed := stableFoldLevel_error step
          simp [stableFoldToRoot, Ssz.foldToRoot, step, failed, Bind.bind, Except.bind]
      | ok stable =>
          obtain ⟨pinned, folded, perm⟩ := stableFoldLevel_success step
          have keys := foldToRoot_success_iff_keys
            (fun i => (perm.map Prod.fst).mem_iff) depth
          simpa [stableFoldToRoot, Ssz.foldToRoot, step, folded, Bind.bind, Except.bind]
            using (ih stable).trans keys

theorem stableFoldToRoot_error {depth : Nat} {nodes : List (Nat × Ssz.Bytes)}
    {reason : Ssz.Err} (failed : stableFoldToRoot depth nodes = .error reason) :
    reason = .proofIncomplete := by
  induction depth generalizing nodes with
  | zero =>
      simp only [stableFoldToRoot] at failed
      cases found : Ssz.nodeAt nodes 1 with
      | none => simpa [found] using failed.symm
      | some value => simp [found] at failed
  | succ depth ih =>
      cases step : stableFoldLevel (depth + 1) nodes with
      | error fault =>
          have same : fault = reason := by
            simpa [stableFoldToRoot, step, Bind.bind, Except.bind] using failed
          rw [← same]
          exact foldLevel_error (stableFoldLevel_error step)
      | ok stable =>
          exact ih (by simpa [stableFoldToRoot, step, Bind.bind, Except.bind] using failed)

/-- Permuting live nodes preserves their supported origins and value agreement;
neither property makes an assumption about a future root or a readable claim. -/
theorem stableFoldToRoot_proofTree {source : List (Nat × Ssz.Bytes)} {height : Nat}
    (separated : Pure.ProofAntichain source) :
    ∀ depth, depth ≤ height → ∀ nodes, Pure.ProofSupported source nodes →
      Pure.NodesAgree (Pure.proofTreeNode source height) nodes → ∀ root,
      stableFoldToRoot depth nodes = .ok root → root = (Pure.proofTree source height 1).root := by
  intro depth
  induction depth with
  | zero =>
      intro bounded nodes supported agree root built
      simp only [stableFoldToRoot] at built
      cases found : Ssz.nodeAt nodes 1 with
      | none => simp [found] at built
      | some value =>
          have same : value = root := by simpa [found] using built
          subst root
          have valueEq := Pure.nodeAt_agrees agree found
          simpa only [Pure.proofTreeNode, Ssz.levelOf,
            show Nat.log2 1 = 0 by decide, Nat.sub_zero] using valueEq
  | succ depth ih =>
      intro bounded nodes supported agree root built
      cases step : stableFoldLevel (depth + 1) nodes with
      | error reason => simp [stableFoldToRoot, step, Bind.bind, Except.bind] at built
      | ok stable =>
          obtain ⟨pinned, folded, perm⟩ := stableFoldLevel_success step
          have pinnedSupported := supported.fold folded
          have pinnedAgree := Pure.foldLevel_proofTree separated supported
            (by omega) bounded agree folded
          have stableSupported : Pure.ProofSupported source stable := by
            intro index member
            exact pinnedSupported index ((perm.map Prod.fst).mem_iff.mp member)
          have stableAgree : Pure.NodesAgree (Pure.proofTreeNode source height) stable := by
            intro index value member
            exact pinnedAgree index value (perm.mem_iff.mp member)
          exact ih (by omega) stable stableSupported stableAgree root
            (by simpa [stableFoldToRoot, step, Bind.bind, Except.bind] using built)

/-- The complete stable logical reducer refines the pinned reducer for arbitrary
raw blobs. Antichain and uniqueness are properties of the supplied indices. -/
theorem stableFoldToRoot_eq {nodes : List (Nat × Ssz.Bytes)}
    (unique : (nodes.map Prod.fst).Nodup) (separated : Pure.ProofAntichain nodes)
    (depth : Nat) : stableFoldToRoot depth nodes = Ssz.foldToRoot depth nodes := by
  have success := stableFoldToRoot_success_iff depth nodes
  cases native : stableFoldToRoot depth nodes with
  | error reason =>
      cases pinned : Ssz.foldToRoot depth nodes with
      | error other => rw [stableFoldToRoot_error native, foldToRoot_error pinned]
      | ok root => simp [native, pinned] at success
  | ok root =>
      cases pinned : Ssz.foldToRoot depth nodes with
      | error reason => simp [native, pinned] at success
      | ok expected =>
          have supported : Pure.ProofSupported nodes nodes := by
            intro index member
            exact ⟨index, member, 0, by simp⟩
          have agree : Pure.NodesAgree (Pure.proofTreeNode nodes depth) nodes := by
            intro index value member
            have found := Pure.nodeAt_of_unique unique member
            unfold Pure.proofTreeNode
            cases remaining : depth - Ssz.levelOf index <;>
              simp [Pure.proofTree, found, Pure.CommitmentTree.root]
          have actualTree := stableFoldToRoot_proofTree separated depth (Nat.le_refl _)
            nodes supported agree root native
          have expectedTree := Pure.foldToRoot_eq_proofTree separated unique pinned
          rw [actualTree, expectedTree]

end SszNative.Proof

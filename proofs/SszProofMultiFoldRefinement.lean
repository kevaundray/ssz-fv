import SszProofMultiInvariant
import SszProofMultiInitial
import SszProofMultiPassRefinementStable

set_option autoImplicit false

namespace SszNative.Proof

/-- Exact computational relation: no exhaustion or representation error is
possible in the allocation-free reducer. -/
def MultiRootRelation : Except Error Ssz.Bytes → Except Ssz.Err Ssz.Bytes → Prop
  | .error reason, expected => reason = .proofIncomplete ∧ expected = .error .proofIncomplete
  | .ok root, expected => expected = .ok root

theorem multiFindRoot_relation {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (nodes : List (MultiNode l p))
    (valid : ∀ node ∈ nodes, node.Valid) :
    MultiRootRelation (multiFindRoot nodes)
      (stableFoldToRoot 0 (nodes.map (MultiNode.erase leaves proof hl hp))) := by
  induction nodes with
  | nil => exact ⟨rfl, rfl⟩
  | cons node rest ih =>
      have head := valid node (by simp)
      have tail : ∀ n ∈ rest, n.Valid := fun n member => valid n (by simp [member])
      by_cases root : node.position = 1
      · obtain ⟨digest, hashed⟩ := node.rootHashed head root
        simp [multiFindRoot, node.isRoot_eq head, root, hashed, stableFoldToRoot,
          Ssz.nodeAt, MultiNode.erase, MultiValue.bytes, MultiRootRelation]
      · simpa [multiFindRoot, node.isRoot_eq head, root, stableFoldToRoot,
          Ssz.nodeAt, MultiNode.erase] using ih tail

theorem multiFold_stable {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (depth : Nat)
    (nodes : List (MultiNode l p)) (valid : ∀ node ∈ nodes, node.Valid) :
    MultiRootRelation (multiFold leaves proof hl hp depth nodes).result
      (stableFoldToRoot depth (nodes.map (MultiNode.erase leaves proof hl hp))) := by
  induction depth generalizing nodes with
  | zero => exact multiFindRoot_relation leaves proof hl hp nodes valid
  | succ depth ih =>
      have step := multiPass_compact_stable leaves proof hl hp (depth + 1) (by omega) nodes valid
      cases passed : (multiPass leaves proof hl hp (depth + 1) nodes).result with
      | error reason =>
          have facts : reason = .proofIncomplete ∧
              stableFoldLevel (depth + 1) (nodes.map (MultiNode.erase leaves proof hl hp)) =
                .error .proofIncomplete := by
            simpa [passed, MultiPassStableRelation] using step
          simp [multiFold, passed, stableFoldToRoot, facts.1, facts.2,
            MultiRootRelation, Bind.bind, Except.bind]
      | ok updated =>
          have pinned : stableFoldLevel (depth + 1)
              (nodes.map (MultiNode.erase leaves proof hl hp)) =
              .ok ((multiCompact (depth + 1) updated).active.map
                (MultiNode.erase leaves proof hl hp)) := by
            simpa [passed, MultiPassStableRelation] using step
          have updatedValid : ∀ node ∈ updated, node.Valid := by
            have same := multiPassWorker_nodes leaves proof hl hp (depth + 1) nodes [] updated passed
            have all := multiPass_valid leaves proof hl hp (depth + 1) nodes valid
            change (multiPass leaves proof hl hp (depth + 1) nodes).nodes = updated at same
            rw [same] at all
            exact all
          have prepared := multiPass_prepared leaves proof hl hp (depth + 1) nodes updated passed
          have compactValid := multiCompactWorker_valid (depth + 1) (by omega) updated 0 0
            updatedValid prepared
          have next := ih (multiCompact (depth + 1) updated).active compactValid
          simpa [multiFold, passed, stableFoldToRoot, pinned, Bind.bind, Except.bind] using next

theorem MultiRootRelation.refines {actual : Except Error Ssz.Bytes}
    {expected : Except Ssz.Err Ssz.Bytes} (related : MultiRootRelation actual expected) :
    ResultRefines Eq actual expected := by
  cases actual with
  | error reason =>
      obtain ⟨rfl, rfl⟩ := related
      exact .error .proofIncomplete .proofIncomplete rfl
  | ok root =>
      change expected = .ok root at related
      rw [related]
      exact .ok root root rfl

/-- Pinned correspondence for arbitrary raw bytes. The only domain is the
current valid original-index views and the supplied unique antichain. -/
theorem multiFold_refines {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (depth : Nat)
    (nodes : List (MultiNode l p)) (valid : ∀ node ∈ nodes, node.Valid)
    (unique : ((nodes.map (MultiNode.erase leaves proof hl hp)).map Prod.fst).Nodup)
    (antichain : Pure.ProofAntichain (nodes.map (MultiNode.erase leaves proof hl hp))) :
    ResultRefines Eq (multiFold leaves proof hl hp depth nodes).result
      (Ssz.foldToRoot depth (nodes.map (MultiNode.erase leaves proof hl hp))) := by
  have related := multiFold_stable leaves proof hl hp depth nodes valid
  rw [stableFoldToRoot_eq unique antichain] at related
  exact related.refines

end SszNative.Proof

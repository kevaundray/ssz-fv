import SszProofMultiPassRefinement
import SszProofMultiView
import SszProofMultiStable

set_option autoImplicit false

namespace SszNative.Proof

/-- Current physical/view invariants discharge the read-after-write condition.
No distinctness or hash injectivity is required. -/
theorem multiSnapshotReadable_valid {l p : Nat} (deepest : Nat)
    (nodes : List (MultiNode l p)) (positive : 0 < deepest)
    (valid : ∀ node ∈ nodes, node.Valid) : MultiSnapshotReadable deepest nodes nodes := by
  intro node member atDepth even sibling found
  exact node.sibling_odd sibling (valid node member)
    (valid sibling (List.mem_of_find?_eq_some found)) (by omega) even
    (List.find?_some found)

/-- Raw first-match selection erases to the pinned first-match lookup. -/
theorem multiSiblingLookup_erase {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (node : MultiNode l p)
    (nodeValid : node.Valid) (deep : 0 < node.depth) (nodes : List (MultiNode l p))
    (valid : ∀ other ∈ nodes, other.Valid) :
    (nodes.find? node.isSiblingOf).map (fun sibling => sibling.value.bytes leaves proof hl hp) =
      Ssz.nodeAt (nodes.map (MultiNode.erase leaves proof hl hp))
        (Ssz.gindexSibling node.position) := by
  induction nodes with
  | nil => rfl
  | cons other rest ih =>
      have otherValid := valid other (List.mem_cons_self)
      have restValid : ∀ next ∈ rest, next.Valid := fun next mem =>
        valid next (List.mem_cons_of_mem other mem)
      have tail := ih restValid
      simp only [Ssz.nodeAt] at tail ⊢
      simp only [List.map_cons, List.find?, MultiNode.erase]
      rw [node.isSiblingOf_eq other nodeValid otherValid deep]
      by_cases paired : Ssz.gindexSibling node.position = other.position
      · simp [paired]
      · have opposite : other.position ≠ Ssz.gindexSibling node.position := Ne.symm paired
        simpa [paired, opposite] using tail

/-- Both errors and successful stable-order outputs are related. This relation
also records that the value pass has no resource or layout failure branch. -/
def MultiPassStableRelation {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) :
    Except Error (List (MultiNode l p)) → Except Ssz.Err (List (Nat × Ssz.Bytes)) → Prop
  | .error reason, pinned => reason = .proofIncomplete ∧ pinned = .error .proofIncomplete
  | .ok nodes, pinned => pinned = .ok (nodes.map (MultiNode.erase leaves proof hl hp))

private theorem shifted_parent {l p : Nat} (node : MultiNode l p) :
    node.index.value >>> (node.shift + 1) = Ssz.gindexParent node.position := by
  rw [Nat.shiftRight_add]
  simp only [MultiNode.position, Ssz.gindexParent, Nat.shiftRight_eq_div_pow, Nat.pow_one]

/-- Erasure of the frozen pass is the stable pinned fold, not the differently
ordered parents-then-kept intermediate list. -/
theorem multiSnapshotFoldNodes_stable {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (deepest : Nat)
    (positive : 0 < deepest) (snapshot pending : List (MultiNode l p))
    (snapshotValid : ∀ node ∈ snapshot, node.Valid)
    (pendingValid : ∀ node ∈ pending, node.Valid) :
    MultiPassStableRelation leaves proof hl hp
      (multiSnapshotFoldNodes leaves proof hl hp deepest snapshot pending)
      (stableFoldLevelNodes deepest (snapshot.map (MultiNode.erase leaves proof hl hp))
        (pending.map (MultiNode.erase leaves proof hl hp))) := by
  induction pending with
  | nil => rfl
  | cons node pending ih =>
      have nodeValid := pendingValid node (List.mem_cons_self)
      have restValid : ∀ other ∈ pending, other.Valid := fun other mem =>
        pendingValid other (List.mem_cons_of_mem node mem)
      have nextRelated := ih restValid
      by_cases atDepth : node.depth = deepest
      · have deep : 0 < node.depth := by omega
        have lookup := multiSiblingLookup_erase leaves proof hl hp node nodeValid deep
          snapshot snapshotValid
        by_cases even : node.position % 2 = 0
        · have left : node.isRight = false := by rw [node.isRight_eq nodeValid]; simp [even]
          have sibling : Ssz.gindexSibling node.position = node.position + 1 := by
            have pair := Ssz.gindexSibling_even even
            omega
          rw [sibling] at lookup
          cases found : snapshot.find? node.isSiblingOf with
          | none =>
              have missing : Ssz.nodeAt (snapshot.map (MultiNode.erase leaves proof hl hp))
                  (node.position + 1) = none := by simpa [found] using lookup.symm
              simp [multiSnapshotFoldNodes, atDepth, found, MultiPassStableRelation,
                stableFoldLevelNodes, MultiNode.erase, ← nodeValid.depth_eq, atDepth,
                even, missing, throw]
          | some other =>
              have present : Ssz.nodeAt (snapshot.map (MultiNode.erase leaves proof hl hp))
                  (node.position + 1) = some (other.value.bytes leaves proof hl hp) := by
                simpa [found] using lookup.symm
              cases next : multiSnapshotFoldNodes leaves proof hl hp deepest snapshot pending with
              | error reason =>
                  have info : reason = .proofIncomplete ∧
                      stableFoldLevelNodes deepest
                        (snapshot.map (MultiNode.erase leaves proof hl hp))
                        (pending.map (MultiNode.erase leaves proof hl hp)) =
                          .error .proofIncomplete := by
                    simpa [next, MultiPassStableRelation] using nextRelated
                  simp [multiSnapshotFoldNodes, atDepth, found, left, next,
                    MultiPassStableRelation, info.1, stableFoldLevelNodes, MultiNode.erase,
                    ← nodeValid.depth_eq, even, present, info.2, Bind.bind, Except.bind]
              | ok nodes =>
                  have info : stableFoldLevelNodes deepest
                      (snapshot.map (MultiNode.erase leaves proof hl hp))
                      (pending.map (MultiNode.erase leaves proof hl hp)) =
                        .ok (nodes.map (MultiNode.erase leaves proof hl hp)) := by
                    simpa [next, MultiPassStableRelation] using nextRelated
                  simp [multiSnapshotFoldNodes, atDepth, found, left, next,
                    MultiPassStableRelation, stableFoldLevelNodes, MultiNode.erase,
                    ← nodeValid.depth_eq, even, present, info, Bind.bind, Except.bind,
                    Pure.pure, Except.pure, MultiNode.position, MultiValue.bytes,
                    shifted_parent node, rawCombine_eq]
        · have odd : node.position % 2 = 1 := by omega
          have right : node.isRight = true := by rw [node.isRight_eq nodeValid]; simp [odd]
          have sibling : Ssz.gindexSibling node.position = node.position - 1 := by
            have pair := Ssz.gindexSibling_odd odd
            omega
          rw [sibling] at lookup
          cases found : snapshot.find? node.isSiblingOf with
          | none =>
              have missing : Ssz.nodeAt (snapshot.map (MultiNode.erase leaves proof hl hp))
                  (node.position - 1) = none := by simpa [found] using lookup.symm
              simp [multiSnapshotFoldNodes, atDepth, found, MultiPassStableRelation,
                stableFoldLevelNodes, MultiNode.erase, ← nodeValid.depth_eq, even, missing, throw]
          | some other =>
              have present : Ssz.nodeAt (snapshot.map (MultiNode.erase leaves proof hl hp))
                  (node.position - 1) = some (other.value.bytes leaves proof hl hp) := by
                simpa [found] using lookup.symm
              simpa [multiSnapshotFoldNodes, atDepth, found, right, stableFoldLevelNodes,
                MultiNode.erase, ← nodeValid.depth_eq, even, present] using nextRelated
      · cases next : multiSnapshotFoldNodes leaves proof hl hp deepest snapshot pending with
        | error reason =>
            have info : reason = .proofIncomplete ∧
                stableFoldLevelNodes deepest (snapshot.map (MultiNode.erase leaves proof hl hp))
                  (pending.map (MultiNode.erase leaves proof hl hp)) =
                    .error .proofIncomplete := by
              simpa [next, MultiPassStableRelation] using nextRelated
            simp [multiSnapshotFoldNodes, atDepth, next, MultiPassStableRelation, info.1,
              stableFoldLevelNodes, MultiNode.erase, ← nodeValid.depth_eq, info.2,
              Bind.bind, Except.bind]
        | ok nodes =>
            have info : stableFoldLevelNodes deepest
                (snapshot.map (MultiNode.erase leaves proof hl hp))
                (pending.map (MultiNode.erase leaves proof hl hp)) =
                  .ok (nodes.map (MultiNode.erase leaves proof hl hp)) := by
              simpa [next, MultiPassStableRelation] using nextRelated
            simp [multiSnapshotFoldNodes, atDepth, next, MultiPassStableRelation,
              stableFoldLevelNodes, MultiNode.erase, ← nodeValid.depth_eq, info,
              Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- The raw in-place value pass and stable compaction implement exactly the
stable pinned level fold under present-slot physical/view invariants. -/
theorem multiPass_compact_stable {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (deepest : Nat)
    (positive : 0 < deepest) (nodes : List (MultiNode l p))
    (valid : ∀ node ∈ nodes, node.Valid) :
    MultiPassStableRelation leaves proof hl hp
      ((multiPass leaves proof hl hp deepest nodes).result.map
        (fun updated => (multiCompact deepest updated).active))
      (stableFoldLevel deepest (nodes.map (MultiNode.erase leaves proof hl hp))) := by
  rw [multiPass_snapshot leaves proof hl hp deepest nodes
    (multiSnapshotReadable_valid deepest nodes positive valid)]
  exact multiSnapshotFoldNodes_stable leaves proof hl hp deepest positive nodes nodes valid valid

/-- Consumer-facing one-step refinement, including the raw missing-sibling
error. The resource-permissive constructor is never used by this pass. -/
theorem multiPass_refines {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (deepest : Nat)
    (nodes : List (MultiNode l p)) (positive : 0 < deepest)
    (valid : ∀ node ∈ nodes, node.Valid) :
    ResultRefines (fun raw logical => raw.map (MultiNode.erase leaves proof hl hp) = logical)
      ((multiPass leaves proof hl hp deepest nodes).result.map
        (fun updated => (multiCompact deepest updated).active))
      (stableFoldLevel deepest (nodes.map (MultiNode.erase leaves proof hl hp))) := by
  have related := multiPass_compact_stable leaves proof hl hp deepest positive nodes valid
  cases actual : (multiPass leaves proof hl hp deepest nodes).result.map
      (fun updated => (multiCompact deepest updated).active) with
  | error reason =>
      have info : reason = .proofIncomplete ∧
          stableFoldLevel deepest (nodes.map (MultiNode.erase leaves proof hl hp)) =
            .error .proofIncomplete := by
        simpa [actual, MultiPassStableRelation] using related
      rw [info.1, info.2]
      exact .error .proofIncomplete .proofIncomplete rfl
  | ok updated =>
      have info : stableFoldLevel deepest (nodes.map (MultiNode.erase leaves proof hl hp)) =
          .ok (updated.map (MultiNode.erase leaves proof hl hp)) := by
        simpa [actual, MultiPassStableRelation] using related
      rw [info]
      exact .ok _ _ rfl

end SszNative.Proof

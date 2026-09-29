import SszProofMultiPureBase

namespace SszNative.Proof.Pure

open Ssz

/-- The finite binary computation induced by an arbitrary proof frontier. -/
inductive CommitmentTree where
  | leaf (node : Bytes)
  | fork (left right : CommitmentTree)

namespace CommitmentTree

def root : CommitmentTree → Bytes
  | .leaf node => node
  | .fork left right => combine left.root right.root

end CommitmentTree

/-- No supplied key is a strict ancestor of another supplied key. -/
def ProofAntichain (nodes : List (Nat × Bytes)) : Prop :=
  ∀ i ∈ nodes.map Prod.fst, ∀ j ∈ nodes.map Prod.fst, ∀ step, i >>> step = j → i = j

def proofTree (nodes : List (Nat × Bytes)) : Nat → Nat → CommitmentTree
  | 0, index => .leaf ((nodeAt nodes index).getD zeroChunk)
  | height + 1, index =>
    match nodeAt nodes index with
    | some value => .leaf value
    | none => .fork (proofTree nodes height (2 * index))
        (proofTree nodes height (2 * index + 1))

def proofTreeNode (source : List (Nat × Bytes)) (height index : Nat) : Bytes :=
  (proofTree source (height - levelOf index) index).root

private theorem proofTree_supplied (source : List (Nat × Bytes)) (height index : Nat)
    {value : Bytes} (found : nodeAt source index = some value) :
    proofTree source height index = .leaf value := by
  cases height <;> simp [proofTree, found]

theorem source_parent_absent {source : List (Nat × Bytes)}
    (separated : ProofAntichain source) {index : Nat}
    (supported : ∃ original ∈ source.map Prod.fst, ∃ step, original >>> step = index)
    (positive : 2 ≤ index) : nodeAt source (gindexParent index) = none := by
  cases found : nodeAt source (gindexParent index) with
  | none => rfl
  | some value =>
    obtain ⟨original, member, step, descended⟩ := supported
    have parentMember := nodeAt_member found
    have named : gindexParent index ∈ source.map Prod.fst :=
      List.mem_map.mpr ⟨_, parentMember, rfl⟩
    have ancestral : original >>> (step + 1) = gindexParent index := by
      rw [shiftRight_succ, descended]
      rfl
    have same := separated original member _ named _ ancestral
    have bounded : original >>> step ≤ original := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_le_self _ _
    unfold gindexParent at same
    omega

theorem proofTree_parent {source : List (Nat × Bytes)} {height index : Nat}
    (positive : 2 ≤ index) (bounded : levelOf index ≤ height) (even : index % 2 = 0)
    (absent : nodeAt source (gindexParent index) = none) :
    proofTree source (height - levelOf (gindexParent index)) (gindexParent index) =
      .fork (proofTree source (height - levelOf index) index)
        (proofTree source (height - levelOf (index + 1)) (index + 1)) := by
  have parentDepth := levelOf_parent positive
  have siblingDepth : levelOf (index + 1) = levelOf index := by
    have pair := gindexSibling_even even
    have sibling : gindexSibling index = index + 1 := by omega
    rw [← sibling]
    exact levelOf_sibling positive
  have budget : height - levelOf (gindexParent index) = height - levelOf index + 1 := by
    change levelOf index = levelOf (gindexParent index) + 1 at parentDepth
    omega
  have left : 2 * gindexParent index = index := by unfold gindexParent; omega
  simp only [budget, proofTree, absent, left, siblingDepth]

private theorem proofTreeNode_parent {source : List (Nat × Bytes)} {height index : Nat}
    (positive : 2 ≤ index) (bounded : levelOf index ≤ height) (even : index % 2 = 0)
    (absent : nodeAt source (gindexParent index) = none) :
    combine (proofTreeNode source height index) (proofTreeNode source height (index + 1)) =
      proofTreeNode source height (gindexParent index) := by
  exact (congrArg CommitmentTree.root (proofTree_parent positive bounded even absent)).symm

/-- Every live key originates from an upward shift of a supplied key. -/
def ProofSupported (source nodes : List (Nat × Bytes)) : Prop :=
  ∀ index ∈ nodes.map Prod.fst,
    ∃ original ∈ source.map Prod.fst, ∃ step, original >>> step = index

theorem ProofSupported.fold {source nodes result : List (Nat × Bytes)} {depth : Nat}
    (supported : ProofSupported source nodes) (folded : foldLevel depth nodes = .ok result) :
    ProofSupported source result := by
  intro index member
  obtain ⟨child, childMember, unchanged | joined⟩ := (foldLevel_indices folded index).mp member
  · exact unchanged.2 ▸ supported child childMember
  · obtain ⟨original, originalMember, step, descended⟩ := supported child childMember
    refine ⟨original, originalMember, step + 1, ?_⟩
    rw [shiftRight_succ, descended]
    exact joined.2.2.symm

private theorem foldLevelNodes_local_agrees {tree : Nat → Bytes} {depth : Nat}
    {nodes pending : List (Nat × Bytes)}
    (parents : ∀ index value, (index, value) ∈ pending → levelOf index = depth →
      index % 2 = 0 → combine (tree index) (tree (index + 1)) = tree (gindexParent index))
    (allAgree : NodesAgree tree nodes) (pendingAgree : NodesAgree tree pending)
    {outParents outKept : List (Nat × Bytes)}
    (folded : foldLevelNodes depth nodes pending = .ok (outParents, outKept)) :
    NodesAgree tree (outParents ++ outKept) := by
  induction pending generalizing outParents outKept with
  | nil =>
    simp [foldLevelNodes] at folded
    rcases folded with ⟨rfl, rfl⟩
    simp [NodesAgree]
  | cons pair rest ih =>
    rcases pair with ⟨index, value⟩
    have head : value = tree index := pendingAgree index value (by simp)
    have tail : NodesAgree tree rest := fun i v member => pendingAgree i v (by simp [member])
    have remaining : ∀ i v, (i, v) ∈ rest → levelOf i = depth → i % 2 = 0 →
        combine (tree i) (tree (i + 1)) = tree (gindexParent i) :=
      fun i v member => parents i v (List.mem_cons_of_mem _ member)
    simp only [foldLevelNodes] at folded
    split at folded
    · cases rec : foldLevelNodes depth nodes rest with
      | error error => simp [rec, Bind.bind, Except.bind] at folded
      | ok result =>
        rcases result with ⟨ps, ks⟩
        simp [rec, Bind.bind, Except.bind, Pure.pure, Except.pure] at folded
        rcases folded with ⟨rfl, rfl⟩
        have agrees := ih remaining tail rec
        intro i v member
        simp only [List.mem_append, List.mem_cons] at member
        rcases member with member | same | member
        · exact agrees i v (by simp [member])
        · cases same; exact head
        · exact agrees i v (by simp [member])
    · rename_i atDepth
      have atDepth : levelOf index = depth := by simpa using atDepth
      split at folded
      · rename_i even
        have even : index % 2 = 0 := by simpa using even
        cases sibling : nodeAt nodes (index + 1) with
        | none => simp [sibling, throw] at folded
        | some siblingValue =>
          have siblingAgrees := nodeAt_agrees allAgree sibling
          cases rec : foldLevelNodes depth nodes rest with
          | error error => simp [sibling, rec, Bind.bind, Except.bind] at folded
          | ok result =>
            rcases result with ⟨ps, ks⟩
            simp [sibling, rec, Bind.bind, Except.bind, Pure.pure, Except.pure] at folded
            rcases folded with ⟨rfl, rfl⟩
            have agrees := ih remaining tail rec
            intro i v member
            simp only [List.mem_append, List.mem_cons] at member
            rcases member with (same | member) | member
            · cases same
              rw [head, siblingAgrees]
              exact parents index value List.mem_cons_self atDepth even
            · exact agrees i v (by simp [member])
            · exact agrees i v (by simp [member])
      · split at folded
        · simp [throw] at folded
        · exact ih remaining tail folded

theorem foldLevel_proofTree {source nodes result : List (Nat × Bytes)} {height depth : Nat}
    (separated : ProofAntichain source) (supported : ProofSupported source nodes)
    (positive : 0 < depth) (bounded : depth ≤ height)
    (agree : NodesAgree (proofTreeNode source height) nodes)
    (folded : foldLevel depth nodes = .ok result) :
    NodesAgree (proofTreeNode source height) result := by
  unfold foldLevel at folded
  cases rec : foldLevelNodes depth nodes nodes with
  | error fault => simp [rec, Bind.bind, Except.bind] at folded
  | ok pair =>
    rcases pair with ⟨parents, kept⟩
    simp [rec, Bind.bind, Except.bind, Pure.pure, Except.pure] at folded
    subst result
    apply foldLevelNodes_local_agrees (tree := proofTreeNode source height) _ agree agree rec
    intro index value member atDepth even
    have low := two_le_of_level_positive atDepth positive
    apply proofTreeNode_parent low (by omega) even
    exact source_parent_absent separated
      (supported index (List.mem_map.mpr ⟨_, member, rfl⟩)) low

theorem foldToRoot_proofTree {source : List (Nat × Bytes)} {height : Nat}
    (separated : ProofAntichain source) :
    ∀ depth, depth ≤ height → ∀ nodes, ProofSupported source nodes →
      NodesAgree (proofTreeNode source height) nodes → ∀ root,
      foldToRoot depth nodes = .ok root → root = (proofTree source height 1).root := by
  intro depth
  induction depth with
  | zero =>
    intro _ nodes _ agree root built
    simp only [foldToRoot] at built
    cases found : nodeAt nodes 1 with
    | none => simp [found] at built
    | some value =>
      simp [found] at built
      subst root
      simpa [proofTreeNode, show levelOf 1 = 0 from rfl] using nodeAt_agrees agree found
  | succ depth ih =>
    intro bounded nodes supported agree root built
    simp only [foldToRoot] at built
    cases folded : foldLevel (depth + 1) nodes with
    | error fault => simp [folded, Bind.bind, Except.bind] at built
    | ok result =>
      simp only [folded, Bind.bind, Except.bind] at built
      exact ih (by omega) result (supported.fold folded)
        (foldLevel_proofTree separated supported (by omega) bounded agree folded) root built

theorem foldToRoot_eq_proofTree {nodes : List (Nat × Bytes)} {height : Nat}
    (separated : ProofAntichain nodes) (unique : (nodes.map Prod.fst).Nodup)
    {root : Bytes} (built : foldToRoot height nodes = .ok root) :
    root = (proofTree nodes height 1).root := by
  apply foldToRoot_proofTree separated height (Nat.le_refl _) nodes _ _ root built
  · intro index member
    exact ⟨index, member, 0, by simp⟩
  · intro index value member
    dsimp only [proofTreeNode]
    rw [proofTree_supplied nodes _ _ (nodeAt_of_unique unique member)]
    rfl

end SszNative.Proof.Pure

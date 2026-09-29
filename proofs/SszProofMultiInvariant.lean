import SszProofMultiView

set_option autoImplicit false

namespace SszNative.Proof

private theorem valid_cons {l p : Nat} {node : MultiNode l p} {nodes : List (MultiNode l p)}
    (head : node.Valid) (tail : ∀ n ∈ nodes, n.Valid) : ∀ n ∈ node :: nodes, n.Valid := by
  intro n member
  rcases List.mem_cons.mp member with rfl | member
  · exact head
  · exact tail n member

theorem multiPassWorker_valid {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (deepest : Nat)
    (pending : List (MultiNode l p)) : ∀ doneRev,
    (∀ node ∈ doneRev, node.Valid) → (∀ node ∈ pending, node.Valid) →
    ∀ node ∈ (multiPassWorker leaves proof hl hp deepest doneRev pending).nodes, node.Valid := by
  induction pending with
  | nil =>
      intro doneRev doneValid pendingValid node member
      exact doneValid node (by simpa [multiPassWorker] using member)
  | cons node pending ih =>
      intro doneRev doneValid pendingValid
      have head := pendingValid node (by simp)
      have tail : ∀ n ∈ pending, n.Valid := fun n member => pendingValid n (by simp [member])
      unfold multiPassWorker
      split
      · exact ih (node :: doneRev) (valid_cons head doneValid) tail
      · split
        · intro n member
          simp only [List.mem_append, List.mem_reverse] at member
          exact member.elim (doneValid n) (pendingValid n)
        · rename_i sibling found
          split
          · exact ih (node :: doneRev) (valid_cons head doneValid) tail
          · exact ih _ (valid_cons (head.hashed _) doneValid) tail

theorem multiPass_valid {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (deepest : Nat)
    (nodes : List (MultiNode l p)) (valid : ∀ node ∈ nodes, node.Valid) :
    ∀ node ∈ (multiPass leaves proof hl hp deepest nodes).nodes, node.Valid :=
  multiPassWorker_valid leaves proof hl hp deepest nodes [] (by simp) valid

/-- Every even slot at the current level has received its hash before compaction. -/
def MultiNode.Prepared {l p : Nat} (depth : Nat) (node : MultiNode l p) : Prop :=
  node.depth = depth → node.isRight = false → ∃ digest, node.value = .hashed digest

private theorem prepared_cons {l p : Nat} {depth : Nat} {node : MultiNode l p}
    {nodes : List (MultiNode l p)} (head : node.Prepared depth)
    (tail : ∀ n ∈ nodes, n.Prepared depth) : ∀ n ∈ node :: nodes, n.Prepared depth := by
  intro n member
  rcases List.mem_cons.mp member with rfl | member
  · exact head
  · exact tail n member

theorem multiPassWorker_prepared {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (deepest : Nat)
    (pending : List (MultiNode l p)) : ∀ doneRev,
    (∀ node ∈ doneRev, node.Prepared deepest) → ∀ updated,
    (multiPassWorker leaves proof hl hp deepest doneRev pending).result = .ok updated →
    ∀ node ∈ updated, node.Prepared deepest := by
  induction pending with
  | nil =>
      intro doneRev prepared updated success
      have same : doneRev.reverse = updated := by simpa [multiPassWorker] using success
      subst updated
      intro node member
      exact prepared node (by simpa using member)
  | cons node pending ih =>
      intro doneRev prepared updated success
      unfold multiPassWorker at success
      split at success
      · rename_i outside
        have head : node.Prepared deepest := by
          intro atDepth even
          simp [atDepth] at outside
        exact ih _ (prepared_cons head prepared) updated success
      · split at success
        · cases success
        · rename_i sibling found
          split at success
          · rename_i odd
            have head : node.Prepared deepest := by
              intro atDepth even
              simp [even] at odd
            exact ih _ (prepared_cons head prepared) updated success
          · have head : ({ node with value := MultiValue.hashed
                (rawCombine (node.value.bytes leaves proof hl hp)
                  (sibling.value.bytes leaves proof hl hp)) } : MultiNode l p).Prepared deepest := by
              intro atDepth even
              exact ⟨_, rfl⟩
            exact ih _ (prepared_cons head prepared) updated success

theorem multiPass_prepared {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (deepest : Nat)
    (nodes updated : List (MultiNode l p))
    (success : (multiPass leaves proof hl hp deepest nodes).result = .ok updated) :
    ∀ node ∈ updated, node.Prepared deepest :=
  multiPassWorker_prepared leaves proof hl hp deepest nodes [] (by simp) updated success

theorem multiPassWorker_nodes {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (deepest : Nat)
    (pending : List (MultiNode l p)) : ∀ doneRev updated,
    (multiPassWorker leaves proof hl hp deepest doneRev pending).result = .ok updated →
    (multiPassWorker leaves proof hl hp deepest doneRev pending).nodes = updated := by
  induction pending with
  | nil => intro doneRev updated success; exact Except.ok.inj success
  | cons node pending ih =>
      intro doneRev updated success
      unfold multiPassWorker at success ⊢
      split at success ⊢
      · exact ih _ _ success
      · split at success ⊢
        · cases success
        · split at success ⊢ <;> exact ih _ _ success

theorem MultiNode.Valid.climb {l p : Nat} {node : MultiNode l p}
    (valid : node.Valid) (positive : 0 < node.depth)
    (hashed : ∃ digest, node.value = .hashed digest) :
    ({ node with shift := node.shift + 1, depth := node.depth - 1 } : MultiNode l p).Valid := by
  have low : 2 ≤ node.position := Pure.two_le_of_level_positive valid.depth_eq.symm positive
  have parentDepth := Pure.levelOf_parent low
  have parent : ({ node with shift := node.shift + 1, depth := node.depth - 1 } :
      MultiNode l p).position = node.position / 2 := by
    exact Ssz.shiftRight_succ node.index.value node.shift
  refine ⟨valid.physical, ?_, ?_, ?_, ?_⟩
  · rw [parent]; omega
  · rw [parent]
    have depth := valid.depth_eq
    dsimp
    omega
  · have shift := valid.shift_eq
    dsimp
    omega
  · obtain ⟨digest, same⟩ := hashed
    simp [same]

theorem multiCompactWorker_valid {l p : Nat} (deepest : Nat) (positive : 0 < deepest)
    (nodes : List (MultiNode l p)) : ∀ position written,
    (∀ node ∈ nodes, node.Valid) → (∀ node ∈ nodes, node.Prepared deepest) →
    ∀ node ∈ (multiCompactWorker deepest position written nodes).active, node.Valid := by
  induction nodes with
  | nil => intro position written valid prepared node member; cases member
  | cons node rest ih =>
      intro position written valid prepared
      have head := valid node (by simp)
      have tail : ∀ n ∈ rest, n.Valid := fun n member => valid n (by simp [member])
      have ready := prepared node (by simp)
      have tailReady : ∀ n ∈ rest, n.Prepared deepest :=
        fun n member => prepared n (by simp [member])
      unfold multiCompactWorker
      split
      · exact ih _ _ tail tailReady
      · rename_i retained
        have kept : (if node.depth == deepest then
            { node with shift := node.shift + 1, depth := node.depth - 1 } else node).Valid := by
          split
          · rename_i same
            have same : node.depth = deepest := by simpa using same
            have even : node.isRight = false := by
              cases parity : node.isRight
              · rfl
              · simp [same, parity] at retained
            exact head.climb (by omega) (ready same even)
          · exact head
        exact valid_cons kept (ih _ _ tail tailReady)

end SszNative.Proof

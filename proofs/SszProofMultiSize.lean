import SszProofMultiInvariant

set_option autoImplicit false

namespace SszNative.Proof

/-- Borrowed raw blobs have no width condition; only owned hash slots do. -/
def MultiNode.HashWidth {l p : Nat} (node : MultiNode l p) : Prop :=
  match node.value with
  | .hashed digest => digest.size = 32
  | _ => True

private theorem width_cons {l p : Nat} {node : MultiNode l p} {nodes : List (MultiNode l p)}
    (head : node.HashWidth) (tail : ∀ n ∈ nodes, n.HashWidth) : ∀ n ∈ node :: nodes, n.HashWidth := by
  intro n member
  rcases List.mem_cons.mp member with rfl | member
  · exact head
  · exact tail n member

theorem multiPassWorker_hashWidth {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (deepest : Nat)
    (pending : List (MultiNode l p)) : ∀ doneRev,
    (∀ node ∈ doneRev, node.HashWidth) → (∀ node ∈ pending, node.HashWidth) →
    ∀ node ∈ (multiPassWorker leaves proof hl hp deepest doneRev pending).nodes, node.HashWidth := by
  induction pending with
  | nil =>
      intro doneRev doneWidth pendingWidth node member
      exact doneWidth node (by simpa [multiPassWorker] using member)
  | cons node pending ih =>
      intro doneRev doneWidth pendingWidth
      have head := pendingWidth node (by simp)
      have tail : ∀ n ∈ pending, n.HashWidth := fun n member => pendingWidth n (by simp [member])
      unfold multiPassWorker
      split
      · exact ih (node :: doneRev) (width_cons head doneWidth) tail
      · split
        · intro n member
          simp only [List.mem_append, List.mem_reverse] at member
          exact member.elim (doneWidth n) (pendingWidth n)
        · rename_i sibling found
          split
          · exact ih (node :: doneRev) (width_cons head doneWidth) tail
          · exact ih _ (width_cons (rawCombine_size _ _) doneWidth) tail

theorem multiCompactWorker_hashWidth {l p : Nat} (deepest : Nat)
    (nodes : List (MultiNode l p)) : ∀ position written,
    (∀ node ∈ nodes, node.HashWidth) →
    ∀ node ∈ (multiCompactWorker deepest position written nodes).active, node.HashWidth := by
  induction nodes with
  | nil => intro position written widths node member; cases member
  | cons node rest ih =>
      intro position written widths
      have head := widths node (by simp)
      have tail : ∀ n ∈ rest, n.HashWidth := fun n member => widths n (by simp [member])
      unfold multiCompactWorker
      split
      · exact ih _ _ tail
      · have kept : (if node.depth == deepest then
            { node with shift := node.shift + 1, depth := node.depth - 1 } else node).HashWidth := by
          split <;> exact head
        exact width_cons kept (ih _ _ tail)

theorem multiFindRoot_success_size {l p : Nat} (nodes : List (MultiNode l p))
    (widths : ∀ node ∈ nodes, node.HashWidth) (root : Ssz.Bytes)
    (success : multiFindRoot nodes = .ok root) : root.size = 32 := by
  induction nodes with
  | nil => cases success
  | cons node rest ih =>
      have head := widths node (by simp)
      have tail : ∀ n ∈ rest, n.HashWidth := fun n member => widths n (by simp [member])
      unfold multiFindRoot at success
      split at success
      · cases value : node.value with
        | hashed digest =>
            have same : digest = root := by simpa [value] using success
            subst root
            simpa [MultiNode.HashWidth, value] using head
        | leaf position => exact ih tail (by simpa [value] using success)
        | proof position => exact ih tail (by simpa [value] using success)
      · exact ih tail success

theorem multiFold_success_size {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (depth : Nat)
    (nodes : List (MultiNode l p)) (widths : ∀ node ∈ nodes, node.HashWidth)
    (root : Ssz.Bytes) (success : (multiFold leaves proof hl hp depth nodes).result = .ok root) :
    root.size = 32 := by
  induction depth generalizing nodes with
  | zero => exact multiFindRoot_success_size nodes widths root success
  | succ depth ih =>
      cases passed : (multiPass leaves proof hl hp (depth + 1) nodes).result with
      | error reason => simp [multiFold, passed] at success
      | ok updated =>
          have updatedWidth : ∀ node ∈ updated, node.HashWidth := by
            have all := multiPassWorker_hashWidth leaves proof hl hp (depth + 1) nodes [] (by simp) widths
            have same := multiPassWorker_nodes leaves proof hl hp (depth + 1) nodes [] updated passed
            rw [same] at all
            exact all
          have compactWidth := multiCompactWorker_hashWidth (depth + 1) updated 0 0 updatedWidth
          exact ih (multiCompact (depth + 1) updated).active compactWidth
            (by simpa [multiFold, passed] using success)

theorem multiInitialNodes_hashWidth (leaves proof : List Ssz.Bytes)
    (indices helpers : List NatOperand) (hl : leaves.length = indices.length)
    (hp : proof.length = helpers.length) :
    ∀ node ∈ multiInitialNodes leaves proof indices helpers hl hp, node.HashWidth := by
  intro node member
  simp only [multiInitialNodes, List.mem_append, List.mem_ofFn] at member
  rcases member with ⟨position, rfl⟩ | ⟨position, rfl⟩ <;> trivial

theorem multiReserved_success_size (leaves proof : List Ssz.Bytes)
    (indices helpers : List NatOperand) (hl : leaves.length = indices.length)
    (hp : proof.length = helpers.length) (layout : TypedArena.Layout)
    (arena : Delimited.ArenaState) (root : Ssz.Bytes)
    (success : (multiReserved leaves proof indices helpers hl hp layout arena).result = .ok root) :
    root.size = 32 := by
  unfold multiReserved at success
  split at success
  · split at success
    · cases success
    · exact multiFold_success_size leaves proof rfl rfl _ _
        (multiInitialNodes_hashWidth leaves proof indices helpers hl hp) root success
  · cases success

/-- Unconditional raw-calculator width: no input blob width or physical-domain
premise is needed. Every accepted root was produced by a full raw hash. -/
theorem calculateMultiMerkleRoot_success_size (leaves proof : List Ssz.Bytes)
    (indices : List NatOperand) (layout : TypedArena.Layout) (arena : Delimited.ArenaState)
    (root : Ssz.Bytes)
    (success : (calculateMultiMerkleRoot leaves proof indices layout arena).result = .ok root) :
    root.size = 32 := by
  unfold calculateMultiMerkleRoot at success
  split at success
  · unfold bind at success
    split at success
    · cases success
    · split at success
      · exact multiReserved_success_size leaves proof indices _ _ _ layout _ root success
      · unfold failCount bind at success
        split at success <;> cases success
  · unfold failCount bind at success
    split at success <;> cases success

theorem calculateNativeMultiMerkleRoot_success_size (leaves proof : List Ssz.Bytes)
    (indices : List NatOperand) (arena : Delimited.ArenaState) (root : Ssz.Bytes)
    (success : (calculateNativeMultiMerkleRoot leaves proof indices arena).result = .ok root) :
    root.size = 32 :=
  calculateMultiMerkleRoot_success_size leaves proof indices nativeNodeLayout arena root success

end SszNative.Proof

import SszProofMultiResources

set_option autoImplicit false

namespace SszNative.Proof

/-- The stable compaction decision for one initialized slot. -/
def multiCompactNode {l p : Nat} (deepest : Nat) (node : MultiNode l p) :
    Option (MultiNode l p) :=
  if node.depth == deepest && node.isRight then none
  else some (if node.depth == deepest then
    { node with shift := node.shift + 1, depth := node.depth - 1 } else node)

theorem multiCompactWorker_active {l p : Nat} (deepest : Nat)
    (nodes : List (MultiNode l p)) : ∀ position written,
    (multiCompactWorker deepest position written nodes).active =
      nodes.filterMap (multiCompactNode deepest) := by
  induction nodes with
  | nil => intro position written; rfl
  | cons node rest ih =>
      intro position written
      unfold multiCompactWorker
      split
      · rename_i dropped
        simpa [List.filterMap_cons, multiCompactNode, dropped] using
          ih (position + 1) written
      · rename_i kept
        simpa [List.filterMap_cons, multiCompactNode, kept] using
          congrArg (fun tail => (if node.depth == deepest then
            { node with shift := node.shift + 1, depth := node.depth - 1 } else node) :: tail)
            (ih (position + 1) (written + 1))

theorem multiCompact_active {l p : Nat} (deepest : Nat)
    (nodes : List (MultiNode l p)) :
    (multiCompact deepest nodes).active = nodes.filterMap (multiCompactNode deepest) :=
  multiCompactWorker_active deepest nodes 0 0

private theorem find_map_projection {α β : Type} (f : α → β) (test : β → Bool)
    (xs : List α) :
    (xs.find? (fun x => test (f x))).map f = (xs.map f).find? test := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.find?, List.map_cons]
      split <;> simp_all

/-- Sibling selection reads only the unchanged view, even when its value was
already overwritten. The odd-value projection additionally identifies every
value that an even writer is permitted to read. -/
theorem multi_find_oddView {l p : Nat} (node : MultiNode l p)
    (first second : List (MultiNode l p))
    (same : first.map MultiNode.oddView = second.map MultiNode.oddView) :
    (first.find? node.isSiblingOf).map MultiNode.oddView =
      (second.find? node.isSiblingOf).map MultiNode.oddView := by
  let test : ((NatOperand × Nat × Nat) × Option (MultiValue l p)) → Bool :=
    fun view => Indices.prefixEqual node.index node.shift true view.1.1 view.1.2.1
  have firstEq := find_map_projection MultiNode.oddView test first
  have secondEq := find_map_projection MultiNode.oddView test second
  change (first.find? node.isSiblingOf).map MultiNode.oddView = _ at firstEq
  change (second.find? node.isSiblingOf).map MultiNode.oddView = _ at secondEq
  rw [firstEq, secondEq, same]

private theorem oddView_right {l p : Nat} {first second : MultiNode l p}
    (same : first.oddView = second.oddView) : first.isRight = second.isRight := by
  have views := congrArg Prod.fst same
  have indices := congrArg Prod.fst views
  have shifts := congrArg (fun view : NatOperand × Nat × Nat => view.2.1) views
  simp only [MultiNode.oddView, MultiNode.view] at indices shifts
  simp only [MultiNode.isRight, indices, shifts]

private theorem oddView_value {l p : Nat} {first second : MultiNode l p}
    (same : first.oddView = second.oddView) (right : second.isRight = true) :
    first.value = second.value := by
  have firstRight : first.isRight = true := (oddView_right same).trans right
  have values := congrArg Prod.snd same
  simpa [MultiNode.oddView, firstRight, right] using values

/-- A functional snapshot formulation of the native pass followed by stable
compaction. Unlike the executable pass, this reads siblings from a fixed list.
It retains the native odd-node existence check and arbitrary raw byte values. -/
def multiSnapshotFoldNodes {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (deepest : Nat)
    (snapshot : List (MultiNode l p)) :
    List (MultiNode l p) → Except Error (List (MultiNode l p))
  | [] => .ok []
  | node :: pending =>
      if node.depth != deepest then
        (multiSnapshotFoldNodes leaves proof hl hp deepest snapshot pending).map (node :: ·)
      else
        match snapshot.find? node.isSiblingOf with
        | none => .error .proofIncomplete
        | some sibling =>
            if node.isRight then
              multiSnapshotFoldNodes leaves proof hl hp deepest snapshot pending
            else
              let digest := rawCombine (node.value.bytes leaves proof hl hp)
                (sibling.value.bytes leaves proof hl hp)
              let parent : MultiNode l p := { node with
                shift := node.shift + 1
                depth := node.depth - 1
                value := (.hashed digest) }
              (multiSnapshotFoldNodes leaves proof hl hp deepest snapshot pending).map
                (parent :: ·)

/-- The only read-after-write obligation: an even node's selected sibling is
odd. There is no injectivity, hash equality, or successful-future-pass premise. -/
def MultiSnapshotReadable {l p : Nat} (deepest : Nat)
    (snapshot pending : List (MultiNode l p)) : Prop :=
  ∀ node ∈ pending, node.depth = deepest → node.isRight = false →
    ∀ sibling, snapshot.find? node.isSiblingOf = some sibling → sibling.isRight = true

private theorem compact_cons_away {l p : Nat} (deepest : Nat) (node : MultiNode l p)
    (away : (node.depth != deepest) = true) : multiCompactNode deepest node = some node := by
  have ne : node.depth ≠ deepest := by simpa using away
  simp [multiCompactNode, ne]

private theorem compact_cons_right {l p : Nat} (deepest : Nat) (node : MultiNode l p)
    (atDepth : ¬ (node.depth != deepest) = true) (right : node.isRight = true) :
    multiCompactNode deepest node = none := by
  have eq : node.depth = deepest := by simpa using atDepth
  simp [multiCompactNode, eq, right]

private theorem compact_cons_left {l p : Nat} (deepest : Nat) (node : MultiNode l p)
    (digest : Ssz.Bytes) (atDepth : ¬ (node.depth != deepest) = true)
    (left : ¬ node.isRight = true) :
    multiCompactNode deepest ({ node with value := (.hashed digest) } : MultiNode l p) =
      some { node with
        shift := node.shift + 1
        depth := node.depth - 1
        value := (.hashed digest) } := by
  have eq : node.depth = deepest := by simpa using atDepth
  have even : node.isRight = false := Bool.eq_false_iff.mpr left
  simp [multiCompactNode, MultiNode.isRight] at even ⊢
  simp [eq, even]

/-- Prefix-parametric proof of the in-place pass. The accumulator is the live,
possibly overwritten prefix; oddViews equality is the complete frame needed
for sibling reads. Error branches are preserved, not ruled out. -/
theorem multiPassWorker_snapshot {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (deepest : Nat)
    (snapshot pending : List (MultiNode l p)) :
    ∀ doneRev,
    (doneRev.reverse ++ pending).map MultiNode.oddView = snapshot.map MultiNode.oddView →
    MultiSnapshotReadable deepest snapshot pending →
    ((multiPassWorker leaves proof hl hp deepest doneRev pending).result.map
      (List.filterMap (multiCompactNode deepest))) =
    (multiSnapshotFoldNodes leaves proof hl hp deepest snapshot pending).map
      (fun rest => doneRev.reverse.filterMap (multiCompactNode deepest) ++ rest) := by
  induction pending with
  | nil => intro doneRev same readable; simp [multiPassWorker, multiSnapshotFoldNodes, Except.map]
  | cons node pending ih =>
      intro doneRev same readable
      have tailReadable : MultiSnapshotReadable deepest snapshot pending := by
        intro other mem atDepth even sibling found
        exact readable other (List.mem_cons_of_mem node mem) atDepth even sibling found
      have moved : ((node :: doneRev).reverse ++ pending).map MultiNode.oddView =
          snapshot.map MultiNode.oddView := by
        simpa [List.reverse_cons, List.append_assoc] using same
      have lookup := multi_find_oddView node (doneRev.reverse ++ node :: pending) snapshot same
      unfold multiPassWorker multiSnapshotFoldNodes
      split
      · rename_i away
        rw [ih (node :: doneRev) moved tailReadable]
        cases next : multiSnapshotFoldNodes leaves proof hl hp deepest snapshot pending <;>
          simp [Except.map, List.reverse_cons, List.filterMap_append,
            compact_cons_away deepest node away, List.append_assoc]
      · rename_i atDepth
        cases live : (doneRev.reverse ++ node :: pending).find? node.isSiblingOf with
        | none =>
            have frozen : snapshot.find? node.isSiblingOf = none := by
              cases found : snapshot.find? node.isSiblingOf <;> simp_all
            simp [frozen, Except.map]
        | some sibling =>
            cases frozen : snapshot.find? node.isSiblingOf with
            | none => simp [live, frozen] at lookup
            | some original =>
                have selected : sibling.oddView = original.oddView := by
                  simpa [live, frozen] using lookup
                dsimp only
                split
                · rename_i right
                  rw [ih (node :: doneRev) moved tailReadable]
                  cases next : multiSnapshotFoldNodes leaves proof hl hp deepest snapshot pending <;>
                    simp [Except.map, List.reverse_cons, List.filterMap_append,
                      compact_cons_right deepest node atDepth right]
                · rename_i left
                  have even : node.isRight = false := Bool.eq_false_iff.mpr left
                  have originalRight := readable node (List.mem_cons_self)
                    (by simpa using atDepth) even original frozen
                  have values : sibling.value = original.value := oddView_value selected originalRight
                  let digest := rawCombine (node.value.bytes leaves proof hl hp)
                    (original.value.bytes leaves proof hl hp)
                  have updated :
                      (({ node with value := .hashed digest } :: doneRev).reverse ++ pending).map
                        MultiNode.oddView = snapshot.map MultiNode.oddView := by
                    have evenBit : Indices.bit node.index node.shift ≠ true := left
                    simpa [List.reverse_cons, List.map_append, List.append_assoc,
                      MultiNode.oddView, MultiNode.view, MultiNode.isRight, evenBit] using same
                  simp only [values]
                  rw [ih ({ node with value := .hashed digest } :: doneRev) updated tailReadable]
                  cases next : multiSnapshotFoldNodes leaves proof hl hp deepest snapshot pending <;>
                    simp [Except.map, List.reverse_cons, List.filterMap_append,
                      compact_cons_left deepest node digest atDepth left, List.append_assoc, digest]

theorem multiPass_snapshot {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (deepest : Nat)
    (nodes : List (MultiNode l p)) (readable : MultiSnapshotReadable deepest nodes nodes) :
    (multiPass leaves proof hl hp deepest nodes).result.map
      (fun updated => (multiCompact deepest updated).active) =
      multiSnapshotFoldNodes leaves proof hl hp deepest nodes nodes := by
  have correspondence :=
    multiPassWorker_snapshot leaves proof hl hp deepest nodes nodes [] rfl readable
  cases result : multiSnapshotFoldNodes leaves proof hl hp deepest nodes nodes <;>
    simpa [multiPass, multiCompact_active, result, Except.map] using correspondence

end SszNative.Proof

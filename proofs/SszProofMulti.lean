import SszProofTypes
import SszIndicesCore
import SszIndicesFrontier

set_option autoImplicit false

namespace SszNative.Proof

/-- Raw operands are borrowed by position; only computed digests are owned. -/
inductive MultiValue (leafCount proofCount : Nat) where
  | leaf (position : Fin leafCount)
  | proof (position : Fin proofCount)
  | hashed (digest : Ssz.Bytes)

def MultiValue.bytes {l p : Nat} (leaves : List Ssz.Bytes) (proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) : MultiValue l p → Ssz.Bytes
  | .leaf position => leaves[position.val]'(by omega)
  | .proof position => proof[position.val]'(by omega)
  | .hashed digest => digest

/-- The original borrowed integer never changes when a node climbs. -/
structure MultiNode (leafCount proofCount : Nat) where
  index : NatOperand
  shift : Nat
  depth : Nat
  value : MultiValue leafCount proofCount

def MultiNode.position {l p : Nat} (node : MultiNode l p) : Nat :=
  node.index.value >>> node.shift

def MultiNode.isRight {l p : Nat} (node : MultiNode l p) : Bool :=
  Indices.bit node.index node.shift

def MultiNode.isSiblingOf {l p : Nat} (node other : MultiNode l p) : Bool :=
  Indices.prefixEqual node.index node.shift true other.index other.shift

def MultiNode.erase {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (node : MultiNode l p) :
    Nat × Ssz.Bytes :=
  (node.position, node.value.bytes leaves proof hl hp)

/-- Writes name slots of the already-reserved node array; none reserve storage. -/
inductive MultiWrite (leafCount proofCount : Nat) where
  | hash (position : Nat) (digest : Ssz.Bytes)
  | climb (position : Nat) (shift depth : Nat)
  | copy (source destination : Nat) (node : MultiNode leafCount proofCount)

structure MultiPassResult (leafCount proofCount : Nat) where
  result : Except Error (List (MultiNode leafCount proofCount))
  /-- On failure, the initialized array including all earlier value writes. -/
  nodes : List (MultiNode leafCount proofCount)
  writes : List (MultiWrite leafCount proofCount)

/-- Left-to-right value pass. `doneRev.reverse ++ pending` is the live array.
Sibling tests use unchanged index/shift/depth fields, including already visited
slots. An odd node is checked but never overwritten. -/
def multiPassWorker {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (deepest : Nat)
    (doneRev : List (MultiNode l p)) : List (MultiNode l p) → MultiPassResult l p
  | [] => ⟨.ok doneRev.reverse, doneRev.reverse, []⟩
  | node :: pending =>
      if node.depth != deepest then
        multiPassWorker leaves proof hl hp deepest (node :: doneRev) pending
      else
        match (doneRev.reverse ++ node :: pending).find? node.isSiblingOf with
        | none => ⟨.error .proofIncomplete, doneRev.reverse ++ node :: pending, []⟩
        | some sibling =>
            if node.isRight then
              multiPassWorker leaves proof hl hp deepest (node :: doneRev) pending
            else
              let digest := rawCombine (node.value.bytes leaves proof hl hp)
                (sibling.value.bytes leaves proof hl hp)
              let next := multiPassWorker leaves proof hl hp deepest
                ({ node with value := .hashed digest } :: doneRev) pending
              { next with writes := .hash doneRev.length digest :: next.writes }

def multiPass {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (deepest : Nat)
    (nodes : List (MultiNode l p)) : MultiPassResult l p :=
  multiPassWorker leaves proof hl hp deepest [] nodes

structure MultiCompactResult (leafCount proofCount : Nat) where
  active : List (MultiNode leafCount proofCount)
  writes : List (MultiWrite leafCount proofCount)

/-- Stable in-place compaction. Source positions advance even when an odd node
is discarded; `written` advances only for a retained slot. -/
def multiCompactWorker {l p : Nat} (deepest position written : Nat) :
    List (MultiNode l p) → MultiCompactResult l p
  | [] => ⟨[], []⟩
  | node :: rest =>
      if node.depth == deepest && node.isRight then
        multiCompactWorker deepest (position + 1) written rest
      else
        let atDepth := node.depth == deepest
        let kept := if atDepth then
          { node with shift := node.shift + 1, depth := node.depth - 1 } else node
        let next := multiCompactWorker deepest (position + 1) (written + 1) rest
        let climbs := if atDepth then [MultiWrite.climb position kept.shift kept.depth] else []
        let copies := if written != position then [MultiWrite.copy position written kept] else []
        ⟨kept :: next.active, climbs ++ copies ++ next.writes⟩

def multiCompact {l p : Nat} (deepest : Nat) (nodes : List (MultiNode l p)) :
    MultiCompactResult l p := multiCompactWorker deepest 0 0 nodes

/-- Final search skips non-hashed root slots exactly as the native loop does. -/
def multiFindRoot {l p : Nat} : List (MultiNode l p) → Except Error Ssz.Bytes
  | [] => .error .proofIncomplete
  | node :: rest =>
      if Indices.prefixEqual node.index node.shift false (.small 1) 0 then
        match node.value with
        | .hashed digest => .ok digest
        | _ => multiFindRoot rest
      else multiFindRoot rest

structure MultiFoldResult (leafCount proofCount : Nat) where
  result : Except Error Ssz.Bytes
  active : List (MultiNode leafCount proofCount)
  writes : List (MultiWrite leafCount proofCount)

/-- Recursion follows the exact decreasing maximum-depth counter, not fuel. -/
def multiFold {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) :
    Nat → List (MultiNode l p) → MultiFoldResult l p
  | 0, nodes => ⟨multiFindRoot nodes, nodes, []⟩
  | deepest + 1, nodes =>
      let passed := multiPass leaves proof hl hp (deepest + 1) nodes
      match passed.result with
      | .error reason => ⟨.error reason, passed.nodes, passed.writes⟩
      | .ok updated =>
          let compacted := multiCompact (deepest + 1) updated
          let next := multiFold leaves proof hl hp deepest compacted.active
          ⟨next.result, next.active, passed.writes ++ compacted.writes ++ next.writes⟩

/-- These lists describe initialized slots, not extra native allocations. -/
def multiInitialNodes (leaves proof : List Ssz.Bytes) (indices helpers : List NatOperand)
    (leafCount : leaves.length = indices.length) (proofCount : proof.length = helpers.length) :
    List (MultiNode leaves.length proof.length) :=
  (List.ofFn fun position : Fin indices.length =>
    let index := indices[position]
    { index := index, shift := 0, depth := Indices.depth index,
      value := .leaf ⟨position.val, by omega⟩ }) ++
  (List.ofFn fun position : Fin helpers.length =>
    let index := helpers[position]
    { index := index, shift := 0, depth := Indices.depth index,
      value := .proof ⟨position.val, by omega⟩ })

def multiInitEffects (pointer : Nat) (indices helpers : List NatOperand) : List Effect :=
  (indices.zipIdx.map fun (index, position) =>
    .nodeInitialized pointer position index 0 (Indices.depth index) (.inl position)) ++
  (helpers.zipIdx.map fun (index, position) =>
    .nodeInitialized pointer (indices.length + position) index 0 (Indices.depth index)
      (.inr position))

/-- Whole typed reservation precedes all node initialization. No initializer can
fail: it only borrows a validated source position and computes integer depth. -/
def multiReserved (leaves proof : List Ssz.Bytes) (indices helpers : List NatOperand)
    (leafCount : leaves.length = indices.length) (proofCount : proof.length = helpers.length)
    (nodeLayout : TypedArena.Layout) (arena : Delimited.ArenaState) : Outcome Ssz.Bytes :=
  let count := indices.length + helpers.length
  if count < 2^64 then
    let reservation := TypedArena.reserve nodeLayout arena.base arena.capacity arena.used count
    match reservation with
    | none => ⟨.error .scratchExhausted, arena.used, [.reserve nodeLayout arena count none]⟩
    | some allocated =>
        let nodes := multiInitialNodes leaves proof indices helpers leafCount proofCount
        let deepest := (nodes.map MultiNode.depth).foldl max 0
        let folded := multiFold leaves proof rfl rfl deepest nodes
        ⟨folded.result, allocated.used,
          .reserve nodeLayout arena count (some allocated) ::
            multiInitEffects allocated.pointer indices helpers⟩
  else unchanged arena.used (.error .scratchExhausted)

/-- Raw reconstruction: count, helper construction, proof count, checked sum,
reservation, initialization, value passes/compaction, and hashed-root search.
No operand width, distinctness, ownership, or aliasing restriction is imposed. -/
def calculateMultiMerkleRoot (leaves proof : List Ssz.Bytes) (indices : List NatOperand)
    (nodeLayout : TypedArena.Layout) (arena : Delimited.ArenaState) : Outcome Ssz.Bytes :=
  if leafCount : leaves.length = indices.length then
    bind (liftIndices arena (Indices.helperIndices indices arena.base arena.capacity arena.used))
      fun helpers used =>
        let nextArena := { arena with used := used }
        if proofCount : proof.length = helpers.values.length then
          multiReserved leaves proof indices helpers.values leafCount proofCount nodeLayout nextArena
        else failCount .proofLength helpers.values.length proof.length nextArena
  else failCount .leafCount indices.length leaves.length arena

/-- Measured by source-exact rustc/QEMU probes on both supported targets.
This layout includes opaque padding, which semantic slot events do not write. -/
def nativeNodeLayout : TypedArena.Layout := ⟨96, 4⟩

def calculateNativeMultiMerkleRoot (leaves proof : List Ssz.Bytes)
    (indices : List NatOperand) (arena : Delimited.ArenaState) : Outcome Ssz.Bytes :=
  calculateMultiMerkleRoot leaves proof indices nativeNodeLayout arena

/-- Folding is completely independent of the arena, including all failure paths. -/
def multiFoldOutcome {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (depth : Nat)
    (nodes : List (MultiNode l p)) (used : Nat) : Outcome Ssz.Bytes :=
  unchanged used (multiFold leaves proof hl hp depth nodes).result

@[simp] theorem multiFoldOutcome_used {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (depth : Nat)
    (nodes : List (MultiNode l p)) (used : Nat) :
    (multiFoldOutcome leaves proof hl hp depth nodes used).used = used := rfl

@[simp] theorem multiFoldOutcome_effects {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (depth : Nat)
    (nodes : List (MultiNode l p)) (used : Nat) :
    (multiFoldOutcome leaves proof hl hp depth nodes used).effects = [] := rfl

/-- Even value replacement never changes the original integer or either view. -/
theorem multi_hash_preserves_view {l p : Nat} (node : MultiNode l p) (digest : Ssz.Bytes) :
    let updated : MultiNode l p := { node with value := MultiValue.hashed digest }
    updated.index = node.index ∧ updated.shift = node.shift ∧ updated.depth = node.depth :=
  ⟨rfl, rfl, rfl⟩

/-- Hashing consumes the complete raw blobs, including empty operands. -/
theorem multi_hash_eq (left right : Ssz.Bytes) : rawCombine left right = Ssz.combine left right :=
  rawCombine_eq left right

end SszNative.Proof

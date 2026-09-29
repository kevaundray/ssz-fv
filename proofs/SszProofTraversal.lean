import SszProofTraversalWindow
import SszProofTraversalRange
import SszIndicesArithmeticPower
import Ssz.Codec.Proof

set_option autoImplicit false

namespace SszNative.Proof

open Codec (Desc Value)

def ceilDepth (capacity : NatOperand) : Nat :=
  let bits := Indices.bitLength capacity
  if bits = 0 then 0 else if Indices.powerOfTwo capacity then bits - 1 else bits

abbrev NodeVisit (view : HashLayout.Layout) :=
  (position : Nat) → (desc : Desc) → (value : Value) →
    view.nested position = some (desc, value) → Nat → Delimited.ArenaState → Outcome Ssz.Bytes

/-- Packed rejection precedes every gap lookup. The supplied index remains the
original borrowed operand, while the callback receives only unconsumed depth. -/
def boundedNode (view : HashLayout.Layout) (index : NatOperand) (depth base treeDepth : Nat)
    (arena : Delimited.ArenaState) (visit : NodeVisit view) : Outcome Ssz.Bytes :=
  if depth ≤ treeDepth then
    let spanDepth := treeDepth - depth
    match boundedStart index depth base spanDepth with
    | none => unchanged arena.used (.ok (MerkleAccumulator.zeroSubtree rawCombine Ssz.zeroChunk spanDepth))
    | some start =>
        if start < view.count then
          rangeRoot view start (boundedStop view.count start spanDepth) spanDepth arena
        else unchanged arena.used (.ok (MerkleAccumulator.zeroSubtree rawCombine Ssz.zeroChunk spanDepth))
  else if view.isPacked then unchanged arena.used (.error .pathIntoPacked)
  else
    let below := depth - treeDepth
    let leaf := (window index below treeDepth).bind (fun position => physicalIndex (base + position))
    match leaf with
    | none => unchanged arena.used (.error .pathIntoGap)
    | some position =>
        match selected : view.nested position with
        | none => unchanged arena.used (.error .pathIntoGap)
        | some (desc, value) => visit position desc value selected below arena

/-- Source conversion precedes min with the physically remaining suffix. -/
def progressiveTake (remaining capacity : Nat) : Nat :=
  min (match physicalIndex capacity with | none => remaining | some capacity => capacity) remaining

theorem progressiveTake_positive (remaining capacity : Nat)
    (nonempty : 0 < remaining) (positive : 0 < capacity) :
    0 < progressiveTake remaining capacity := by
  cases converted : physicalIndex capacity with
  | none =>
      simpa only [progressiveTake, converted, Nat.min_self] using nonempty
  | some held =>
      have same := (physicalIndex_some capacity held converted).1
      simp only [progressiveTake, converted]
      omega

/-- Recursive calls occur only for a nonterminal suffix. The measure is the
number of actual leaves left; huge logical capacities require no padded array. -/
def progressiveFrom (view : HashLayout.Layout) (start capacity : Nat)
    (positive : 0 < capacity) (arena : Delimited.ArenaState) : Outcome Ssz.Bytes :=
  if nonempty : start < view.count then
    let take := progressiveTake (view.count - start) capacity
    bind (rangeRoot view start (start + take) capacity.log2 arena) fun left used =>
      if start + take = view.count then unchanged used (.ok (rawCombine left Ssz.zeroChunk))
      else
        bind (progressiveFrom view (start + take) (capacity * 4) (by omega)
          { arena with used := used }) fun right used =>
            unchanged used (.ok (rawCombine left right))
  else unchanged arena.used (.ok Ssz.zeroChunk)
termination_by view.count - start
decreasing_by
  have step := progressiveTake_positive (view.count - start) capacity (by omega) positive
  omega

/-- The structural depth recursion is the native spine loop: reaching its zero
terminator is legal, taking any further turn there is PathPastSpine. -/
def progressiveNodeFrom (view : HashLayout.Layout) (index : NatOperand) (visit : NodeVisit view) :
    (depth start capacity : Nat) → (positive : 0 < capacity) →
      Delimited.ArenaState → Outcome Ssz.Bytes
  | 0, start, capacity, positive, arena =>
      if start < view.count then progressiveFrom view start capacity positive arena
      else unchanged arena.used (.ok Ssz.zeroChunk)
  | depth + 1, start, capacity, positive, arena =>
      if start ≥ view.count then unchanged arena.used (.error .pathPastSpine)
      else if !Indices.bit index depth then boundedNode view index depth start capacity.log2 arena visit
      else progressiveNodeFrom view index visit depth (start + capacity) (capacity * 4) (by omega) arena

def progressiveNode (view : HashLayout.Layout) (index : NatOperand) (depth : Nat)
    (arena : Delimited.ArenaState) (visit : NodeVisit view) : Outcome Ssz.Bytes :=
  progressiveNodeFrom view index visit depth 0 1 (by decide) arena

abbrev ValueVisit (value : Value) :=
  (child : Value) → child ∈ value.children → Desc → Nat → Delimited.ArenaState → Outcome Ssz.Bytes

/-- Planning, including all arithmetic scratch, is committed before mixin path
inspection. Full-depth zero calls the complete structural root operation. -/
def nodeStep (desc : Desc) (value : Value) (index : NatOperand) (fullDepth : Nat)
    (arena : Delimited.ArenaState) (visit : ValueVisit value) : Outcome Ssz.Bytes :=
  if fullDepth = 0 then liftLayout arena (HashLayout.hashTreeRoot desc value arena)
  else
    let planned := HashLayout.layout desc value arena
    match success : planned.result with
    | .error reason => ⟨.error (.layout reason), planned.used,
        (liftLayout arena planned).effects⟩
    | .ok view =>
        let cursor := { arena with used := planned.used }
        let visitNode : NodeVisit view := fun position childDesc child selected depth childArena =>
          visit child (HashLayout.Layout.Generated.at_child desc value view
            (HashLayout.layout_generated desc value arena view success)
            position childDesc child selected) childDesc depth childArena
        let contents := fun depth => match view.limit with
          | some capacity => boundedNode view index depth 0 (ceilDepth capacity) cursor visitNode
          | none => progressiveNode view index depth cursor visitNode
        let answer := match view.mixin with
          | none => contents fullDepth
          | some word =>
              let remaining := fullDepth - 1
              if Indices.bit index remaining then
                if remaining ≠ 0 then unchanged cursor.used (.error .pathIntoMixin)
                else unchanged cursor.used (.ok word)
              else contents remaining
        ⟨answer.result, answer.used, (liftLayout arena planned).effects ++ answer.effects⟩

/-- Value recursion proves termination independently of declared metadata,
index magnitude, and the pinned specification's separate recursion budget. -/
def nodeAt (desc : Desc) (value : Value) (index : NatOperand) (fullDepth : Nat)
    (arena : Delimited.ArenaState) : Outcome Ssz.Bytes :=
  nodeStep desc value index fullDepth arena
    (fun child _ childDesc depth childArena => nodeAt childDesc child index depth childArena)
termination_by value.nesting
decreasing_by exact Value.child_nesting_lt _ _ (by assumption)

/-- Zero is rejected before layout. One is a valid node read, unlike a proof
request, and retains every effect of the complete hash-tree-root operation. -/
def nodeRoot (desc : Desc) (value : Value) (index : NatOperand)
    (arena : Delimited.ArenaState) : Outcome Ssz.Bytes :=
  if index.wordCount = 0 then unchanged arena.used (.error (.indices (.notAGindex index)))
  else nodeAt desc value index (Indices.depth index) arena

theorem nodeRoot_zero (desc : Desc) (value : Value) (index : NatOperand)
    (arena : Delimited.ArenaState) (zero : index.value = 0) :
    nodeRoot desc value index arena = unchanged arena.used (.error (.indices (.notAGindex index))) := by
  simp [nodeRoot, (Indices.wordCount_zero_iff index).mpr zero]

theorem nodeAt_root (desc : Desc) (value : Value) (index : NatOperand)
    (arena : Delimited.ArenaState) :
    nodeAt desc value index 0 arena = liftLayout arena (HashLayout.hashTreeRoot desc value arena) := by
  rw [nodeAt]
  simp only [nodeStep, ↓reduceIte]

theorem nodeRoot_one (desc : Desc) (value : Value) (index : NatOperand)
    (arena : Delimited.ArenaState) (one : index.value = 1) :
    nodeRoot desc value index arena = liftLayout arena (HashLayout.hashTreeRoot desc value arena) := by
  have nonzero : index.wordCount ≠ 0 := by
    intro zero
    have := (Indices.wordCount_zero_iff index).mp zero
    omega
  have oneDepth : Nat.log2 1 = 0 := by decide
  simp only [nodeRoot, nonzero, ↓reduceIte, Indices.depth_value, one, oneDepth]
  exact nodeAt_root desc value index arena

theorem boundedNode_packed_first (view : HashLayout.Layout) (index : NatOperand)
    (depth base treeDepth : Nat) (arena : Delimited.ArenaState) (visit : NodeVisit view)
    (deep : treeDepth < depth) (packed : view.isPacked = true) :
    boundedNode view index depth base treeDepth arena visit =
      unchanged arena.used (.error .pathIntoPacked) := by
  simp [boundedNode, Nat.not_le.mpr deep, packed]

theorem progressiveNodeFrom_past (view : HashLayout.Layout) (index : NatOperand)
    (visit : NodeVisit view) (depth start capacity : Nat) (positive : 0 < capacity)
    (arena : Delimited.ArenaState) (past : view.count ≤ start) :
    progressiveNodeFrom view index visit (depth + 1) start capacity positive arena =
      unchanged arena.used (.error .pathPastSpine) := by
  simp [progressiveNodeFrom, past]

theorem progressiveNodeFrom_terminator (view : HashLayout.Layout) (index : NatOperand)
    (visit : NodeVisit view) (start capacity : Nat) (positive : 0 < capacity)
    (arena : Delimited.ArenaState) (past : view.count ≤ start) :
    progressiveNodeFrom view index visit 0 start capacity positive arena =
      unchanged arena.used (.ok Ssz.zeroChunk) := by
  simp [progressiveNodeFrom, Nat.not_lt.mpr past]

end SszNative.Proof

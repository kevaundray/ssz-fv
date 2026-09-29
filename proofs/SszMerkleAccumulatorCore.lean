import Ssz.Merkle.Merkleize

set_option autoImplicit false

namespace SszNative.MerkleAccumulator

variable {α : Type}

/-- The native pointer width bounds physical storage, never logical depth. -/
def treeLevels : Nat := 64

def maxCount : Nat := 2 ^ treeLevels - 1

/-- Exactly 64 cells. Inactive cells retain their previous contents. -/
structure Accumulator (α : Type) where
  nodes : Fin 64 → α
  count : Nat

/-- Physical representation obligation, separate from logical tree capacity. -/
def Accumulator.Physical (state : Accumulator α) : Prop :=
  state.count ≤ maxCount

def new (zero : α) : Accumulator α := ⟨fun _ => zero, 0⟩

/-- Total reading outside the concrete slots is only used by mathematical loops.
All native accesses are proved to have an index below 64. -/
def slot (zero : α) (state : Accumulator α) (height : Nat) : α :=
  if valid : height < 64 then state.nodes ⟨height, valid⟩ else zero

/-- Scan low bits in the same increasing order as trailing_ones/trailing_zeros.
The fuel is physical word width, not a cap on final tree depth. -/
def scanRun (count : Nat) (bit : Bool) : Nat → Nat → Nat
  | height, 0 => height
  | height, fuel + 1 =>
      if count.testBit height = bit then scanRun count bit (height + 1) fuel
      else height

def trailingOnes (count : Nat) : Nat := scanRun count true 0 64

def trailingZeros (count : Nat) : Nat := scanRun count false 0 64

/-- Ascending left-node fold; no slot is cleared while a carry propagates. -/
def carry (hash : α → α → α) (zero : α) (state : Accumulator α)
    (node : α) : Nat → α
  | 0 => node
  | height + 1 => hash (slot zero state height) (carry hash zero state node height)

/-- The caller supplies count < usize::MAX. Exactly one cell is written. -/
def pushNode (hash : α → α → α) (zero : α) (state : Accumulator α)
    (node : α) : Accumulator α :=
  let height := trailingOnes state.count
  let folded := carry hash zero state node height
  ⟨fun index => if index.val = height then folded else state.nodes index,
    state.count + 1⟩

/-- Repeated zero hashing uses constant storage. -/
def advanceZero (hash : α → α → α) : Nat → α → α
  | 0, node => node
  | fuel + 1, node => advanceZero hash fuel (hash node node)

def zeroSubtree (hash : α → α → α) (zero : α) (depth : Nat) : α :=
  advanceZero hash depth zero

structure ZeroCursor (α : Type) where
  node : α
  depth : Nat

/-- Remaining has the initial rightmost occupied bit removed. A zero cursor is
advanced only on the padding branch and only as far as the current height. -/
def rootFold (hash : α → α → α) (zero : α) (state : Accumulator α)
    (remaining : Nat) : Nat → Nat → α → ZeroCursor α → α
  | _, 0, node, _ => node
  | height, fuel + 1, node, cursor =>
      if height < 64 ∧ remaining.testBit height = true then
        rootFold hash zero state remaining (height + 1) fuel
          (hash (slot zero state height) node) cursor
      else
        let padding := advanceZero hash (height - cursor.depth) cursor.node
        rootFold hash zero state remaining (height + 1) fuel
          (hash node padding) ⟨padding, height⟩

/-- No complete tree, padding array, or storage exponential in depth is built. -/
def rootAtDepth (hash : α → α → α) (zero : α) (state : Accumulator α)
    (depth : Nat) : α :=
  if state.count = 0 then zeroSubtree hash zero depth
  else
    let height := trailingZeros state.count
    let remaining := state.count &&& (state.count - 1)
    rootFold hash zero state remaining height (depth - height)
      (slot zero state height) ⟨zero, 0⟩

/-- An occupied cell names its aligned completed block of original leaves.
Nothing is required of stale inactive cells. -/
def Occupied (hash : α → α → α) (zero : α) (chunks : Array α)
    (state : Accumulator α) : Prop :=
  state.count = chunks.size ∧ state.Physical ∧
    ∀ height : Fin 64, state.count.testBit height.val = true →
      state.nodes height = Ssz.subtreeRoot hash height.val
        (fun index => Ssz.padded zero chunks
          (state.count / 2 ^ (height.val + 1) * 2 ^ (height.val + 1) + index))

/-- Actual repeated private pushes; public callers separately check physical size. -/
def accumulate (hash : α → α → α) (zero : α) (chunks : List α) : Accumulator α :=
  chunks.foldl (pushNode hash zero) (new zero)

@[simp] theorem new_count (zero : α) : (new zero).count = 0 := rfl

@[simp] theorem pushNode_count (hash : α → α → α) (zero : α)
    (state : Accumulator α) (node : α) :
    (pushNode hash zero state node).count = state.count + 1 := rfl

/-- Retaining inactive cells is part of the executable state update, not merely
an observational equivalence after discarding them. -/
theorem pushNode_unchanged (hash : α → α → α) (zero : α)
    (state : Accumulator α) (node : α) (index : Fin 64)
    (different : index.val ≠ trailingOnes state.count) :
    (pushNode hash zero state node).nodes index = state.nodes index := by
  simp only [pushNode, different, ↓reduceIte]

theorem new_occupied (hash : α → α → α) (zero : α) :
    Occupied hash zero #[] (new zero) := by
  refine ⟨rfl, Nat.zero_le _, ?_⟩
  intro height occupied
  simp [new] at occupied

theorem advanceZero_add (hash : α → α → α) (first second : Nat) (node : α) :
    advanceZero hash (first + second) node =
      advanceZero hash second (advanceZero hash first node) := by
  induction first generalizing node with
  | zero => simp only [Nat.zero_add, advanceZero]
  | succ first ih =>
      simp only [Nat.succ_add, advanceZero]
      exact ih (hash node node)

theorem zeroSubtree_eq_zeroRoot (hash : α → α → α) (zero : α) (depth : Nat) :
    zeroSubtree hash zero depth = Ssz.zeroRoot hash zero depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      change advanceZero hash (depth + 1) zero = _
      rw [advanceZero_add]
      change hash (zeroSubtree hash zero depth) (zeroSubtree hash zero depth) = _
      rw [ih]
      rfl

end SszNative.MerkleAccumulator

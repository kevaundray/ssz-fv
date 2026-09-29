import SszMerkleAccumulatorRefinement

set_option autoImplicit false

namespace SszNative.MerkleProgressive

variable {α : Type}

structure Accumulator (α : Type) where
  completed : Fin 32 → α
  levels : Nat
  current : MerkleAccumulator.Accumulator α
  count : Nat

def new (zero : α) : Accumulator α :=
  ⟨fun _ => zero, 0, MerkleAccumulator.new zero, 0⟩

def Accumulator.Physical (state : Accumulator α) : Prop :=
  state.levels ≤ 32 ∧ state.count ≤ MerkleAccumulator.maxCount ∧
    state.current.count ≤ state.count

/-- Reset only the occupancy map; all 64 current cells survive. -/
def close (state : Accumulator α) (inside : 2 * state.levels < 64) : Accumulator α :=
  { state with
    completed := fun index => if index.val = state.levels then
      state.current.nodes ⟨2 * state.levels, inside⟩ else state.completed index
    levels := state.levels + 1
    current := { state.current with count := 0 } }

/-- Both counters advance before the native completion test. -/
def pushNode (hash : α → α → α) (zero : α) (state : Accumulator α)
    (node : α) : Accumulator α :=
  let next := { state with
    current := MerkleAccumulator.pushNode hash zero state.current node
    count := state.count + 1 }
  if inside : 2 * state.levels < 64 then
    if next.current.count = 2 ^ (2 * state.levels) then close next inside else next
  else next

def push (hash : α → α → α) (zero : α) (state : Accumulator α) (node : α) :
    Accumulator α × Except MerkleAccumulator.Error Unit :=
  if state.count = MerkleAccumulator.maxCount then (state, .error .outputTooSmall)
  else (pushNode hash zero state node, .ok ())

/-- The recursion unfolds the descending native completed-slot loop. -/
def foldCompleted (hash : α → α → α) (zero : α) (nodes : Fin 32 → α) : Nat → α → α
  | 0, root => root
  | level + 1, root =>
    foldCompleted hash zero nodes level
      (hash (if inside : level < 32 then nodes ⟨level, inside⟩ else zero) root)

def finish (hash : α → α → α) (zero : α) (state : Accumulator α) : α :=
  let root := if state.current.count = 0 then zero else
    hash (MerkleAccumulator.rootAtDepth hash zero state.current (2 * state.levels)) zero
  foldCompleted hash zero state.completed state.levels root

def accumulate (hash : α → α → α) (zero : α) (chunks : List α) : Accumulator α :=
  chunks.foldl (pushNode hash zero) (new zero)

def progressive (hash : α → α → α) (zero : α) (chunks : Array α) : α :=
  if chunks.isEmpty then zero else finish hash zero (accumulate hash zero chunks.toList)

theorem close_current_nodes (state : Accumulator α) (inside : 2 * state.levels < 64) :
    (close state inside).current.nodes = state.current.nodes := rfl

theorem close_inactive (state : Accumulator α) (inside : 2 * state.levels < 64)
    (index : Fin 32) (different : index.val ≠ state.levels) :
    (close state inside).completed index = state.completed index := by
  simp only [close, different, ↓reduceIte]

theorem pushNode_current_nodes (hash : α → α → α) (zero : α)
    (state : Accumulator α) (node : α) :
    (pushNode hash zero state node).current.nodes =
      (MerkleAccumulator.pushNode hash zero state.current node).nodes := by
  unfold pushNode
  dsimp only
  split
  · split <;> rfl
  · rfl

@[simp] theorem pushNode_count (hash : α → α → α) (zero : α)
    (state : Accumulator α) (node : α) :
    (pushNode hash zero state node).count = state.count + 1 := by
  unfold pushNode
  dsimp only
  split
  · split <;> rfl
  · rfl

theorem push_full (hash : α → α → α) (zero : α) (state : Accumulator α)
    (node : α) (full : state.count = MerkleAccumulator.maxCount) :
    push hash zero state node = (state, .error .outputTooSmall) := by
  simp only [push, full, ↓reduceIte]

theorem push_room (hash : α → α → α) (zero : α) (state : Accumulator α)
    (node : α) (room : state.count < MerkleAccumulator.maxCount) :
    push hash zero state node = (pushNode hash zero state node, .ok ()) := by
  simp only [push, Nat.ne_of_lt room, ↓reduceIte]

end SszNative.MerkleProgressive

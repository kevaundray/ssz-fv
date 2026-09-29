import SszMerkleAccumulatorCore
import SszMerkleAccumulatorDepth

set_option autoImplicit false

namespace SszNative.MerkleAccumulator

variable {α : Type}

/-- The full-count check precedes the carry fold. On refusal every slot and the
count are unchanged, and the native error is OutputTooSmall. -/
def push (hash : α → α → α) (zero : α) (state : Accumulator α) (node : α) :
    Accumulator α × Except Error Unit :=
  if state.count = maxCount then (state, .error .outputTooSmall)
  else (pushNode hash zero state node, .ok ())

def finish (hash : α → α → α) (zero : α) (state : Accumulator α)
    (limit : Option NatOperand) : Except Error α := do
  let depth ← boundedDepth state.count limit
  return rootAtDepth hash zero state depth

/-- Keep the small natural operands of the exact native undersized-depth error.
In particular this is not an OutputTooSmall error. -/
def finishDepth (hash : α → α → α) (zero : α) (state : Accumulator α)
    (depth : Nat) : Except Error α :=
  if depth < depthForCount state.count then
    .error (.merkleizeLimit (.small (BitVec.ofNat 64 state.count))
      (.small (BitVec.ofNat 64 (2 ^ depth))))
  else .ok (rootAtDepth hash zero state depth)

/-- Validate capacity before hashing even a single input leaf. The concrete
slice length restriction belongs to the refinement premise, not this capacity. -/
def bounded (hash : α → α → α) (zero : α) (chunks : Array α)
    (limit : Option NatOperand) : Except Error α := do
  let depth ← boundedDepth chunks.size limit
  if chunks.isEmpty then
    return zeroSubtree hash zero depth
  else
    return rootAtDepth hash zero (accumulate hash zero chunks.toList) depth

@[simp] theorem push_full (hash : α → α → α) (zero : α)
    (state : Accumulator α) (node : α) (full : state.count = maxCount) :
    push hash zero state node = (state, .error .outputTooSmall) := by
  simp only [push, full, ↓reduceIte]

@[simp] theorem push_room (hash : α → α → α) (zero : α)
    (state : Accumulator α) (node : α) (room : state.count < maxCount) :
    push hash zero state node = (pushNode hash zero state node, .ok ()) := by
  have different : state.count ≠ maxCount := Nat.ne_of_lt room
  simp only [push, different, ↓reduceIte]

theorem finishDepth_undersized (hash : α → α → α) (zero : α)
    (state : Accumulator α) (depth : Nat) (small : depth < depthForCount state.count) :
    finishDepth hash zero state depth =
      .error (.merkleizeLimit (.small (BitVec.ofNat 64 state.count))
        (.small (BitVec.ofNat 64 (2 ^ depth)))) := by
  simp only [finishDepth, small, ↓reduceIte]

theorem finishDepth_sufficient (hash : α → α → α) (zero : α)
    (state : Accumulator α) (depth : Nat) (fits : depthForCount state.count ≤ depth) :
    finishDepth hash zero state depth = .ok (rootAtDepth hash zero state depth) := by
  have enough : ¬depth < depthForCount state.count := Nat.not_lt.mpr fits
  simp only [finishDepth, enough, ↓reduceIte]

/-- A rejected bound cannot reach either zero hashing or leaf hashing. -/
theorem bounded_refuses_before_hashing (hash : α → α → α) (zero : α)
    (chunks : Array α) (limit : Option NatOperand) (reason : Error)
    (refused : boundedDepth chunks.size limit = .error reason) :
    bounded hash zero chunks limit = .error reason := by
  unfold bounded
  rw [refused]
  all_goals rfl

theorem finish_refuses_before_hashing (hash : α → α → α) (zero : α)
    (state : Accumulator α) (limit : Option NatOperand) (reason : Error)
    (refused : boundedDepth state.count limit = .error reason) :
    finish hash zero state limit = .error reason := by
  unfold finish
  rw [refused]
  all_goals rfl

/-- Even noncanonical capacities are returned unchanged on the first error. -/
theorem bounded_undersized (hash : α → α → α) (zero : α) (chunks : Array α)
    (capacity : NatOperand) (undersize : capacity.value < chunks.size) :
    bounded hash zero chunks (some capacity) =
      .error (.merkleizeLimit (.small (BitVec.ofNat 64 chunks.size)) capacity) :=
  bounded_refuses_before_hashing hash zero chunks (some capacity) _
    (boundedDepth_error chunks.size capacity undersize)

theorem finish_undersized (hash : α → α → α) (zero : α) (state : Accumulator α)
    (capacity : NatOperand) (undersize : capacity.value < state.count) :
    finish hash zero state (some capacity) =
      .error (.merkleizeLimit (.small (BitVec.ofNat 64 state.count)) capacity) :=
  finish_refuses_before_hashing hash zero state (some capacity) _
    (boundedDepth_error state.count capacity undersize)

end SszNative.MerkleAccumulator

import SszMerkleProgressive

set_option autoImplicit false

namespace SszNative.MerkleProgressive

variable {α : Type}

theorem width_eq (level : Nat) : 4 ^ level = 2 ^ (2 * level) := by
  rw [Nat.pow_mul]

/-- A completed prefix is partitioned into full, successively wider subtrees.
Inactive completed slots impose no obligations. -/
inductive Prefix (hash : α → α → α) (zero : α) (nodes : Fin 32 → α) :
    List α → Nat → Prop
  | nil : Prefix hash zero nodes [] 0
  | snoc {chunks block : List α} {level : Nat}
      (previous : Prefix hash zero nodes chunks level)
      (inside : level < 32)
      (full : block.length = 2 ^ (2 * level))
      (root : nodes ⟨level, inside⟩ =
        Ssz.subtreeRoot hash (2 * level) (Ssz.padded zero block.toArray)) :
      Prefix hash zero nodes (chunks ++ block) (level + 1)

theorem Prefix.congr {hash : α → α → α} {zero : α} {old fresh : Fin 32 → α}
    {chunks : List α} {level : Nat} (valid : Prefix hash zero old chunks level)
    (same : ∀ index : Fin 32, index.val < level → fresh index = old index) :
    Prefix hash zero fresh chunks level := by
  induction valid with
  | nil => exact .nil
  | @snoc chunks block level previous inside full root ih =>
    exact .snoc (ih (fun index below => same index (by omega))) inside full
      ((same ⟨level, inside⟩ (Nat.lt_succ_self level)).trans root)

/-- The current logical width is a natural number, including 2^64 at level 32.
Only actual occupancy is physically bounded. -/
def Invariant (hash : α → α → α) (zero : α) (chunks : List α)
    (state : Accumulator α) : Prop :=
  state.Physical ∧ state.count = chunks.length ∧
    ∃ before pending : List α,
      chunks = before ++ pending ∧
      Prefix hash zero state.completed before state.levels ∧
      MerkleAccumulator.Occupied hash zero pending.toArray state.current ∧
      pending.length < 2 ^ (2 * state.levels)

theorem new_invariant (hash : α → α → α) (zero : α) :
    Invariant hash zero [] (new zero) := by
  refine ⟨⟨Nat.zero_le 32, Nat.zero_le _, Nat.le_refl _⟩, rfl, [], [], rfl,
    .nil, ?_, Nat.two_pow_pos 0⟩
  exact MerkleAccumulator.new_occupied hash zero

/-- Clearing count makes arbitrary stale nodes valid for the empty suffix. -/
theorem reset_occupied (hash : α → α → α) (zero : α)
    (state : MerkleAccumulator.Accumulator α) :
    MerkleAccumulator.Occupied hash zero #[] { state with count := 0 } := by
  refine ⟨rfl, Nat.zero_le _, ?_⟩
  intro height present
  simp at present

/-- A full occupied cell is precisely the subtree being completed. -/
theorem full_cell (hash : α → α → α) (zero : α) (chunks : Array α)
    (state : MerkleAccumulator.Accumulator α) (depth : Nat) (inside : depth < 64)
    (valid : MerkleAccumulator.Occupied hash zero chunks state)
    (full : state.count = 2 ^ depth) :
    state.nodes ⟨depth, inside⟩ = Ssz.subtreeRoot hash depth (Ssz.padded zero chunks) := by
  have bit : state.count.testBit depth = true := by
    rw [full, Nat.testBit_eq_decide_div_mod_eq, Nat.div_self (Nat.two_pow_pos depth)] <;> rfl
  have cell := valid.2.2 ⟨depth, inside⟩ bit
  have less : 2 ^ depth < 2 ^ (depth + 1) := by
    have positive := Nat.two_pow_pos depth
    rw [Nat.pow_succ]
    omega
  simpa only [full, Nat.div_eq_of_lt less, Nat.zero_mul, Nat.zero_add] using cell

/-- Every successful private transition establishes a fresh decomposition;
there is no hypothesis about any future state or finishing result. -/
theorem pushNode_invariant (hash : α → α → α) (zero : α) (chunks : List α)
    (state : Accumulator α) (node : α) (valid : Invariant hash zero chunks state)
    (room : state.count < MerkleAccumulator.maxCount) :
    Invariant hash zero (chunks ++ [node]) (pushNode hash zero state node) := by
  obtain ⟨physical, count, before, pending, decomposition, completed, occupied, pendingFits⟩ := valid
  have currentCount : state.current.count = pending.length := by simpa using occupied.1
  have currentRoom : state.current.count < MerkleAccumulator.maxCount :=
    Nat.lt_of_le_of_lt physical.2.2 room
  have nextOccupied : MerkleAccumulator.Occupied hash zero (pending ++ [node]).toArray
      (MerkleAccumulator.pushNode hash zero state.current node) := by
    simpa using MerkleAccumulator.pushNode_occupied hash zero pending.toArray
      state.current node occupied currentRoom
  have nextLength : (pending ++ [node]).length = state.current.count + 1 := by
    simp only [List.length_append, List.length_singleton, currentCount]
  have nextCount : state.count + 1 = (chunks ++ [node]).length := by simp [count]
  have nextBound : state.count + 1 ≤ MerkleAccumulator.maxCount := by omega
  have currentBound : state.current.count + 1 ≤ state.count + 1 :=
    Nat.add_le_add_right physical.2.2 1
  have nextDecomposition : chunks ++ [node] = before ++ (pending ++ [node]) := by
    rw [decomposition, List.append_assoc]
  unfold pushNode
  dsimp only
  split
  · rename_i inside
    split
    · rename_i full
      change state.current.count + 1 = 2 ^ (2 * state.levels) at full
      have levelBound : state.levels < 32 := by omega
      have stored := full_cell hash zero (pending ++ [node]).toArray
        (MerkleAccumulator.pushNode hash zero state.current node) (2 * state.levels)
        inside nextOccupied full
      refine ⟨⟨by dsimp [close]; omega, nextBound, Nat.zero_le _⟩, nextCount,
        before ++ (pending ++ [node]), [], ?_, ?_, ?_, ?_⟩
      · simpa only [List.append_nil] using nextDecomposition
      · refine Prefix.snoc (block := pending ++ [node]) (level := state.levels)
          (previous := ?_) (inside := levelBound) (full := nextLength.trans full) (root := ?_)
        · apply completed.congr
          intro index below
          exact close_inactive
            ⟨state.completed, state.levels,
              MerkleAccumulator.pushNode hash zero state.current node, state.count + 1⟩
            inside index (Nat.ne_of_lt below)
        · simpa only [close, ↓reduceIte] using stored
      · exact reset_occupied hash zero _
      · exact Nat.two_pow_pos _
    · rename_i notFull
      change state.current.count + 1 ≠ 2 ^ (2 * state.levels) at notFull
      refine ⟨⟨physical.1, nextBound, currentBound⟩, nextCount,
        before, pending ++ [node], nextDecomposition, completed, nextOccupied, ?_⟩
      rw [nextLength]
      change state.current.count + 1 < 2 ^ (2 * state.levels)
      omega
  · rename_i outside
    have logicalLarge : 2 ^ 64 ≤ 2 ^ (2 * state.levels) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have physicallySmall : state.current.count + 1 < 2 ^ 64 := by
      unfold MerkleAccumulator.maxCount MerkleAccumulator.treeLevels at nextBound
      omega
    refine ⟨⟨physical.1, nextBound, currentBound⟩, nextCount,
      before, pending ++ [node], nextDecomposition, completed, nextOccupied, ?_⟩
    rw [nextLength]
    exact Nat.lt_of_lt_of_le physicallySmall logicalLarge

theorem foldl_invariant (hash : α → α → α) (zero : α) (chunks suffix : List α)
    (state : Accumulator α) (valid : Invariant hash zero chunks state)
    (physical : chunks.length + suffix.length ≤ MerkleAccumulator.maxCount) :
    Invariant hash zero (chunks ++ suffix) (suffix.foldl (pushNode hash zero) state) := by
  induction suffix generalizing chunks state with
  | nil => simpa using valid
  | cons node suffix ih =>
    have room : state.count < MerkleAccumulator.maxCount := by
      have count := valid.2.1
      simp only [List.length_cons] at physical
      omega
    have pushed := pushNode_invariant hash zero chunks state node valid room
    have bound : (chunks ++ [node]).length + suffix.length ≤ MerkleAccumulator.maxCount := by
      simp only [List.length_append, List.length_cons, List.length_nil] at *
      omega
    simpa only [List.foldl_cons, List.append_assoc, List.singleton_append] using
      ih (chunks ++ [node]) (pushNode hash zero state node) pushed bound

theorem accumulate_invariant (hash : α → α → α) (zero : α) (chunks : List α)
    (physical : chunks.length ≤ MerkleAccumulator.maxCount) :
    Invariant hash zero chunks (accumulate hash zero chunks) := by
  simpa only [List.nil_append, accumulate] using
    foldl_invariant hash zero [] chunks (new zero) (new_invariant hash zero)
      (by simpa only [List.length_nil, Nat.zero_add] using physical)

theorem push_invariant (hash : α → α → α) (zero : α) (chunks : List α)
    (state : Accumulator α) (node : α) (valid : Invariant hash zero chunks state) :
    if state.count = MerkleAccumulator.maxCount then
      push hash zero state node = (state, .error .outputTooSmall)
    else (push hash zero state node).2 = .ok () ∧
      Invariant hash zero (chunks ++ [node]) (push hash zero state node).1 := by
  split
  · rename_i full
    exact push_full hash zero state node full
  · rename_i notFull
    have room : state.count < MerkleAccumulator.maxCount := by
      have bound := valid.1.2.1
      omega
    rw [push_room hash zero state node room]
    exact ⟨rfl, pushNode_invariant hash zero chunks state node valid room⟩

end SszNative.MerkleProgressive

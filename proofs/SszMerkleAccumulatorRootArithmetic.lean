import SszMerkleAccumulatorPushArithmetic

namespace SszNative.MerkleAccumulator

/-- The aligned block containing a particular leaf. -/
def rootBlock (index height : Nat) : Nat := index / 2 ^ height * 2 ^ height

theorem root_mod_pow_of_low_bits (count height : Nat)
    (clear : ∀ index, index < height → count.testBit index = false) :
    count % 2 ^ height = 0 := by
  induction height with
  | zero => exact Nat.mod_one count
  | succ height ih =>
      have lower := ih (fun index below => clear index (by omega))
      have bit := clear height (by omega)
      have parity : count / 2 ^ height % 2 = 0 := by
        have bound := Nat.mod_lt (count / 2 ^ height) (by decide : 0 < 2)
        rw [Nat.testBit_eq_decide_div_mod_eq] at bit
        have different := of_decide_eq_false bit
        omega
      rw [Nat.pow_succ, Nat.mod_mul, lower, parity]
      simp

theorem trailingZeros_spec (count : Nat) (nonzero : count ≠ 0)
    (physical : count < 2 ^ 64) :
    trailingZeros count < 64 ∧ count.testBit (trailingZeros count) = true ∧
      count % 2 ^ trailingZeros count = 0 := by
  obtain ⟨lower, upper, clear, stop⟩ := scanRun_spec count false 0 64
  change 0 ≤ trailingZeros count at lower
  change trailingZeros count ≤ 0 + 64 at upper
  have zeros : count % 2 ^ trailingZeros count = 0 :=
    root_mod_pow_of_low_bits count (trailingZeros count)
      (fun index below => clear index (Nat.zero_le _) below)
  have below : trailingZeros count < 64 := by
    by_cases notBelow : trailingZeros count < 64
    · exact notBelow
    · have eq : trailingZeros count = 64 := by omega
      rw [eq, Nat.mod_eq_of_lt physical] at zeros
      exact False.elim (nonzero zeros)
  refine ⟨below, ?_, zeros⟩
  have different := stop (by simpa only [trailingZeros, Nat.zero_add] using below)
  change count.testBit (trailingZeros count) ≠ false at different
  cases value : count.testBit (trailingZeros count) <;> simp_all

theorem root_pred_div (count divisor : Nat) (positive : 0 < divisor)
    (remainder : 0 < count % divisor) :
    (count - 1) / divisor = count / divisor := by
  have decomposition := Nat.mod_add_div count divisor
  have upper := Nat.lt_div_mul_add (a := count) positive
  apply Nat.div_eq_of_lt_le
  · rw [Nat.mul_comm] at decomposition
    omega
  · rw [Nat.add_mul, Nat.one_mul]
    omega

theorem root_boundary_succ (count height : Nat)
    (boundary : 0 < count % 2 ^ (height + 1)) :
    0 < count % 2 ^ (height + 1 + 1) := by
  rw [Nat.pow_succ, Nat.mod_mul]
  omega

theorem root_remaining_bit (count height : Nat)
    (boundary : 0 < count % 2 ^ (height + 1)) :
    (count &&& (count - 1)).testBit height = (count - 1).testBit height := by
  rw [Nat.testBit_and]
  cases bit : (count - 1).testBit height with
  | false => simp
  | true =>
      have quotients := root_pred_div count (2 ^ (height + 1))
        (Nat.two_pow_pos _) boundary
      rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul,
        ← Nat.div_div_eq_div_mul] at quotients
      have monotone : (count - 1) / 2 ^ height ≤ count / 2 ^ height :=
        Nat.div_le_div_right (Nat.sub_le _ _)
      have parity : (count - 1) / 2 ^ height % 2 = 1 := by
        rw [Nat.testBit_eq_decide_div_mod_eq] at bit
        exact of_decide_eq_true bit
      have other : count / 2 ^ height % 2 = 1 := by omega
      simp [Nat.testBit_eq_decide_div_mod_eq, other]

theorem root_remaining_branch (count height : Nat)
    (physical : count < 2 ^ 64)
    (boundary : 0 < count % 2 ^ (height + 1)) :
    (height < 64 ∧ (count &&& (count - 1)).testBit height = true) ↔
      (count - 1).testBit height = true := by
  rw [root_remaining_bit count height boundary]
  constructor
  · exact And.right
  · intro bit
    refine ⟨?_, bit⟩
    by_cases notBelow : height < 64
    · exact notBelow
    · have capacity : 2 ^ 64 ≤ 2 ^ height :=
        Nat.pow_le_pow_of_le (by decide) (by omega)
      have clear := Nat.testBit_lt_two_pow
        (x := count - 1) (i := height) (by omega)
      rw [clear] at bit
      contradiction

theorem rootBlock_step (index height : Nat) :
    rootBlock index height = rootBlock index (height + 1) +
      (index / 2 ^ height % 2) * 2 ^ height := by
  unfold rootBlock
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  have decomposition := congrArg (fun value => value * 2 ^ height)
    (Nat.mod_add_div (index / 2 ^ height) 2)
  rw [Nat.add_mul] at decomposition
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
    Nat.add_comm] using decomposition.symm

theorem rootBlock_step_true (index height : Nat) (bit : index.testBit height = true) :
    rootBlock index height = rootBlock index (height + 1) + 2 ^ height := by
  have parity : index / 2 ^ height % 2 = 1 := by
    rw [Nat.testBit_eq_decide_div_mod_eq] at bit
    exact of_decide_eq_true bit
  rw [rootBlock_step, parity, Nat.one_mul]

theorem rootBlock_step_false (index height : Nat) (bit : index.testBit height = false) :
    rootBlock index height = rootBlock index (height + 1) := by
  have parity : index / 2 ^ height % 2 = 0 := by
    have bound := Nat.mod_lt (index / 2 ^ height) (by decide : 0 < 2)
    rw [Nat.testBit_eq_decide_div_mod_eq] at bit
    have different := of_decide_eq_false bit
    omega
  rw [rootBlock_step, parity, Nat.zero_mul, Nat.add_zero]

theorem root_initial_block (count height : Nat)
    (clear : count % 2 ^ height = 0) (bit : count.testBit height = true) :
    rootBlock (count - 1) height = count / 2 ^ (height + 1) * 2 ^ (height + 1) ∧
      0 < count % 2 ^ (height + 1) ∧ 2 ^ height ≤ count := by
  have positive := Nat.two_pow_pos height
  have parity : count / 2 ^ height % 2 = 1 := by
    rw [Nat.testBit_eq_decide_div_mod_eq] at bit
    exact of_decide_eq_true bit
  have remainder : count % 2 ^ (height + 1) = 2 ^ height := by
    rw [Nat.pow_succ, Nat.mod_mul, clear, parity]
    simp
  have decomposition := Nat.mod_add_div count (2 ^ (height + 1))
  rw [remainder, Nat.mul_comm (2 ^ (height + 1))] at decomposition
  have base : (count / 2 ^ (height + 1) * 2) * 2 ^ height =
      count / 2 ^ (height + 1) * 2 ^ (height + 1) := by
    rw [Nat.pow_succ]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have quotient : (count - 1) / 2 ^ height = count / 2 ^ (height + 1) * 2 := by
    apply Nat.div_eq_of_lt_le
    · rw [base]
      omega
    · rw [Nat.add_mul, Nat.one_mul, base]
      omega
  refine ⟨?_, ?_, ?_⟩
  · unfold rootBlock
    rw [quotient, base]
  · rw [remainder]
    exact positive
  · omega

end SszNative.MerkleAccumulator

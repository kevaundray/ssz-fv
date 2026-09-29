import SszMerkleAccumulatorCore

namespace SszNative.MerkleAccumulator

/-- The scan reports the first differing bit, or the exhausted endpoint. -/
theorem scanRun_spec (count : Nat) (bit : Bool) (height fuel : Nat) :
    height ≤ scanRun count bit height fuel ∧
    scanRun count bit height fuel ≤ height + fuel ∧
    (∀ index, height ≤ index → index < scanRun count bit height fuel →
      count.testBit index = bit) ∧
    (scanRun count bit height fuel < height + fuel →
      count.testBit (scanRun count bit height fuel) ≠ bit) := by
  induction fuel generalizing height with
  | zero =>
      simp only [scanRun, Nat.add_zero]
      exact ⟨Nat.le_refl _, Nat.le_refl _, by omega, by omega⟩
  | succ fuel ih =>
      by_cases same : count.testBit height = bit
      · simp only [scanRun, same, ↓reduceIte]
        obtain ⟨lower, upper, before, stop⟩ := ih (height + 1)
        refine ⟨by omega, by omega, ?_, ?_⟩
        · intro index lo hi
          by_cases eq : index = height
          · simpa [eq] using same
          · exact before index (by omega) hi
        · intro short
          exact stop (by omega)
      · simp only [scanRun, same, ↓reduceIte]
        exact ⟨Nat.le_refl _, by omega, by omega, fun _ => same⟩

theorem trailingOnes_spec (count : Nat) (room : count < maxCount) :
    trailingOnes count < 64 ∧
    (∀ index, index < trailingOnes count → count.testBit index = true) ∧
    count.testBit (trailingOnes count) = false := by
  obtain ⟨_, upper, before, stop⟩ := scanRun_spec count true 0 64
  change trailingOnes count ≤ 64 at upper
  have low : ∀ index, index < trailingOnes count → count.testBit index = true :=
    fun index hi => before index (Nat.zero_le _) hi
  have bound : trailingOnes count < 64 := by
    apply Decidable.byContradiction
    intro not_lt
    have full : trailingOnes count = 64 := by omega
    have mask_le : 2 ^ 64 - 1 ≤ count := by
      apply Nat.le_of_testBit
      intro index present
      simp only [Nat.testBit_two_pow_sub_one, decide_eq_true_eq] at present
      exact low index (by omega)
    unfold maxCount treeLevels at room
    omega
  refine ⟨bound, low, ?_⟩
  have differs := stop (by simpa [trailingOnes] using bound)
  cases eq : count.testBit (trailingOnes count) <;> simp_all [trailingOnes]

/-- All the low carry bits form precisely the low-bit mask. -/
theorem mod_pow_eq_mask (count height : Nat)
    (ones : ∀ index, index < height → count.testBit index = true) :
    count % 2 ^ height = 2 ^ height - 1 := by
  apply Nat.eq_of_testBit_eq
  intro index
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases below : index < height
  · simp [below, ones index below]
  · simp [below]

theorem succ_testBit_below_run (count height index : Nat)
    (ones : ∀ i, i < height → count.testBit i = true) (below : index < height) :
    (count + 1).testBit index = false := by
  have mask := mod_pow_eq_mask count height ones
  have positive := Nat.two_pow_pos height
  have cleared : (count + 1) % 2 ^ height = 0 := by
    rw [← Nat.mod_add_mod, mask, Nat.sub_add_cancel (by omega : 1 ≤ 2 ^ height)]
    exact Nat.mod_self _
  have bits := congrArg (fun n => n.testBit index) cleared
  simpa [Nat.testBit_mod_two_pow, below] using bits

/-- A zero bit prevents an increment from carrying into any higher quotient. -/
theorem succ_div_pow_eq (count stop height : Nat)
    (zero_bit : count.testBit stop = false) (above : stop < height) :
    (count + 1) / 2 ^ height = count / 2 ^ height := by
  have positive := Nat.two_pow_pos height
  have rem_lt := Nat.mod_lt count positive
  have not_mask : count % 2 ^ height ≠ 2 ^ height - 1 := by
    intro mask
    have bits := congrArg (fun n => n.testBit stop) mask
    simp [Nat.testBit_mod_two_pow, above, zero_bit] at bits
  have small : count % 2 ^ height + 1 < 2 ^ height := by omega
  have decomp : count + 1 = (count % 2 ^ height + 1) +
      2 ^ height * (count / 2 ^ height) := by
    have := Nat.mod_add_div count (2 ^ height)
    omega
  rw [decomp, Nat.add_mul_div_left _ _ positive, Nat.div_eq_of_lt small]
  simp

theorem succ_testBit_above_run (count stop height : Nat)
    (zero_bit : count.testBit stop = false) (above : stop < height) :
    (count + 1).testBit height = count.testBit height := by
  simp only [Nat.testBit_eq_decide_div_mod_eq,
    succ_div_pow_eq count stop height zero_bit above]

/-- Adjacent aligned block origins differ by the quotient's low bit. -/
theorem block_base_step (count height : Nat) :
    count / 2 ^ height * 2 ^ height =
      count / 2 ^ (height + 1) * 2 ^ (height + 1) +
        (count / 2 ^ height % 2) * 2 ^ height := by
  have decomp := congrArg (fun n => n * 2 ^ height)
    (Nat.mod_add_div (count / 2 ^ height) 2)
  rw [Nat.add_mul] at decomp
  have quot : count / 2 ^ (height + 1) = count / 2 ^ height / 2 := by
    rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  rw [quot, Nat.pow_succ]
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm] using decomp.symm

theorem block_base_of_bit (count height : Nat) (bit : Bool)
    (present : count.testBit height = bit) :
    count / 2 ^ height * 2 ^ height =
      count / 2 ^ (height + 1) * 2 ^ (height + 1) + bit.toNat * 2 ^ height := by
  rw [block_base_step, ← Nat.toNat_testBit, present]

theorem occupied_block_before (count height : Nat)
    (present : count.testBit height = true) :
    count / 2 ^ (height + 1) * 2 ^ (height + 1) + 2 ^ height ≤ count := by
  have split := block_base_of_bit count height true present
  simp only [Bool.toNat_true, Nat.one_mul] at split
  rw [← split]
  exact Nat.div_mul_le_self _ _

end SszNative.MerkleAccumulator

import SszIndicesProgressiveSemanticBorrow
import SszIndicesProgressiveSemanticThreshold
import SszIndicesArithmeticResources

set_option autoImplicit false

namespace SszNative.Indices.ProgressiveSemantic

/-- The three fields assembled by the native initializer, still as bitwise OR. -/
def maskedValue (level residue : Nat) : Nat :=
  residue ||| ((2 ^ level - 1) * 2 ^ (2 * level + 1)) ||| 2 ^ (2 * level + level + 2)

theorem maskedValue_bit (level residue bit : Nat) :
    (maskedValue level residue).testBit bit =
      (residue.testBit bit || decide (2 * level + 1 ≤ bit ∧ bit < 2 * level + level + 1) ||
        decide (bit = 2 * level + level + 2)) := by
  simp only [maskedValue, Nat.testBit_or, Nat.testBit_mul_two_pow,
    Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow]
  have middle : (decide (2 * level + 1 ≤ bit) && decide (bit - (2 * level + 1) < level)) =
      decide (2 * level + 1 ≤ bit ∧ bit < 2 * level + level + 1) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  rw [middle]
  have last : decide (2 * level + level + 2 = bit) =
      decide (bit = 2 * level + level + 2) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact eq_comm
  rw [last]

private theorem bounded_or_two_pow (value bits : Nat) (inside : value < 2 ^ bits) :
    value ||| 2 ^ bits = value + 2 ^ bits := by
  have disjoint := Nat.two_pow_add_eq_or_of_lt inside 1
  simp only [Nat.mul_one] at disjoint
  calc
    value ||| 2 ^ bits = 2 ^ bits ||| value := Nat.or_comm _ _
    _ = 2 ^ bits + value := disjoint.symm
    _ = value + 2 ^ bits := Nat.add_comm _ _

theorem maskedValue_eq (level residue : Nat) (inside : residue < 2 ^ (2 * level)) :
    maskedValue level residue = upperMasks level + residue := by
  have wider : residue < 2 ^ (2 * level + 1) :=
    Nat.lt_of_lt_of_le inside (Nat.pow_le_pow_right (by decide) (by omega))
  have positive : 1 ≤ 2 ^ level := Nat.one_le_two_pow
  have combined : (2 ^ level - 1) * 2 ^ (2 * level + 1) + residue <
      2 ^ level * 2 ^ (2 * level + 1) := by
    calc
      _ < (2 ^ level - 1) * 2 ^ (2 * level + 1) + 2 ^ (2 * level + 1) :=
        Nat.add_lt_add_left wider _
      _ = 2 ^ level * 2 ^ (2 * level + 1) := by
        rw [← Nat.add_one_mul, Nat.sub_add_cancel positive]
  have high : 2 ^ level * 2 ^ (2 * level + 1) ≤ 2 ^ (2 * level + level + 2) := by
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  unfold maskedValue
  rw [Nat.or_comm residue, Nat.mul_comm (2 ^ level - 1),
    ← Nat.two_pow_add_eq_or_of_lt wider,
    bounded_or_two_pow _ _ (by simpa only [Nat.mul_comm] using Nat.lt_of_lt_of_le combined high)]
  unfold upperMasks
  ac_rfl

theorem maskedValue_bound (level residue : Nat) (inside : residue < 2 ^ (2 * level)) :
    maskedValue level residue < 2 ^ (2 * level + level + 3) := by
  apply Nat.lt_pow_two_of_testBit
  intro bit beyond
  rw [maskedValue_bit]
  have clear : residue.testBit bit = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le inside
      (Nat.pow_le_pow_right (by decide) (by omega)))
  simp [clear, show ¬(2 * level + 1 ≤ bit ∧ bit < 2 * level + level + 1) by omega,
    show bit ≠ 2 * level + level + 2 by omega]

theorem progressiveStep_semantic (chunk : NatOperand) (level residue position : Nat)
    (borrow : Bool) (invariant : BorrowInvariant chunk.value (offset level) residue position borrow) :
    (∀ bit, bit < 64 →
      (progressiveStep chunk (2 * level) position borrow).1.getLsbD bit =
        (maskedValue level residue).testBit (64 * position + bit)) ∧
      BorrowInvariant chunk.value (offset level) residue (position + 1)
        (progressiveStep chunk (2 * level) position borrow).2 := by
  have transition := borrow_transition chunk.value (offset level) residue position borrow
    (word chunk position) (thresholdWord (2 * level) position)
    (word_toNat chunk position) (thresholdWord_even level position) invariant
  refine ⟨?_, ?_⟩
  · intro bit inside
    rw [progressiveStep_word]
    simp only [show 2 * level / 2 = level by omega, BitVec.getLsbD_or]
    rw [← BitVec.testBit_toNat, transition.1, Nat.testBit_mod_two_pow,
      Nat.testBit_div_two_pow]
    simp only [inside, decide_true, Bool.true_and]
    rw [rangeWord_bit position (2 * level + 1) (2 * level + level + 1) bit inside,
      rangeWord_bit position (2 * level + level + 2) (2 * level + level + 2 + 1) bit inside,
      maskedValue_bit]
    have last : (2 * level + level + 2 ≤ 64 * position + bit ∧
        64 * position + bit < 2 * level + level + 2 + 1) ↔
        64 * position + bit = 2 * level + level + 2 := by omega
    simp only [last, Nat.add_comm bit (64 * position)]
  · simpa only [progressiveStep_borrow] using transition.2

/-- The borrow invariant follows the actual ascending initializer, independently
of the mask bits written into prior output slots. -/
theorem fillWords_bits (chunk : NatOperand) (level residue position count : Nat)
    (borrow : Bool) (invariant : BorrowInvariant chunk.value (offset level) residue position borrow)
    (index bit : Nat) (within : index < count) (inside : bit < 64) :
    (((fillWords (progressiveStep chunk (2 * level)) position count borrow).1[index]?).getD 0).getLsbD bit =
      (maskedValue level residue).testBit (64 * (position + index) + bit) := by
  induction count generalizing position borrow index with
  | zero => omega
  | succ count ih =>
      have step := progressiveStep_semantic chunk level residue position borrow invariant
      cases index with
      | zero =>
          simpa only [fillWords, List.getElem?_cons_zero, Option.getD_some, Nat.add_zero] using step.1 bit inside
      | succ index =>
          simp only [fillWords, List.getElem?_cons_succ]
          have rest := ih (position + 1) (progressiveStep chunk (2 * level) position borrow).2
            step.2 index (by omega)
          simpa only [Nat.add_assoc, Nat.add_comm 1 index] using rest

theorem fillWords_value (chunk : NatOperand) (level count : Nat)
    (lower : offset level ≤ chunk.value) (upper : chunk.value < offset (level + 1))
    (enough : 2 * level + level + 3 ≤ 64 * count) :
    Limbs.value (fillWords (progressiveStep chunk (2 * level)) 0 count false).1 =
      Ssz.progressiveChunkGindex chunk.value := by
  have inside : chunk.value - offset level < 2 ^ (2 * level) := by
    rw [offset_succ, width_eq] at upper
    omega
  have bound := maskedValue_bound level (chunk.value - offset level) inside
  have target : maskedValue level (chunk.value - offset level) = Ssz.progressiveChunkGindex chunk.value := by
    rw [maskedValue_eq level _ inside, closed_of_interval chunk.value level lower upper]
  rw [← target]
  apply Nat.eq_of_testBit_eq
  intro bit
  rw [NatShift.limbs_testBit]
  by_cases within : bit / 64 < count
  · have selected := fillWords_bits chunk level (chunk.value - offset level) 0 count false
      (borrow_initial chunk.value (offset level) lower) (bit / 64) (bit % 64) within
      (Nat.mod_lt _ (by decide))
    have decomposition : 64 * (bit / 64) + bit % 64 = bit := by omega
    simpa only [Nat.zero_add, decomposition] using selected
  · rw [List.getElem?_eq_none (by rw [fillWords_length]; omega)]
    simp only [Option.getD_none]
    rw [← BitVec.testBit_toNat, show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_testBit]
    have beyond : 2 * level + level + 3 ≤ bit := by omega
    have clear : (maskedValue level (chunk.value - offset level)).testBit bit = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le bound
        (Nat.pow_le_pow_right (by decide) beyond))
    exact clear.symm

end SszNative.Indices.ProgressiveSemantic

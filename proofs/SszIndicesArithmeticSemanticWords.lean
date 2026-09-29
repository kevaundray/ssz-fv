import SszIndicesArithmeticSemanticCore
import SszNatShiftSemantics

set_option autoImplicit false

namespace SszNative.Indices

theorem word_toNat (index : NatOperand) (position : Nat) :
    (word index position).toNat = (index.value / 2 ^ (64 * position)) % 2 ^ 64 := by
  apply Nat.eq_of_testBit_eq
  intro offset
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases inside : offset < 64
  · simp only [inside, decide_true, Bool.true_and]
    rw [word_eq, limbs_word_bit index.words position offset inside]
    congr 1
    omega
  · simp only [inside, decide_false, Bool.false_and]
    apply Nat.testBit_lt_two_pow
    exact Nat.lt_of_lt_of_le (word index position).isLt
      (Nat.pow_le_pow_right (by decide) (by omega))

theorem word_bit (index : NatOperand) (position offset : Nat) (inside : offset < 64) :
    (word index position).getLsbD offset = index.value.testBit (64 * position + offset) := by
  rw [word_eq]
  exact NatShift.word_bit index position offset inside

theorem word_past_storage (index : NatOperand) (position : Nat)
    (past : index.words.length ≤ position) : word index position = 0 := by
  rw [word_eq, List.getElem?_eq_none (by omega)]
  rfl

theorem lowMask_toNat (bits : Nat) (bounded : bits ≤ 64) :
    (lowMask bits).toNat = 2 ^ bits - 1 := by
  by_cases full : bits = 64
  · simp [lowMask, full, BitVec.neg_one_eq_allOnes]
  · have small : bits < 64 := by omega
    have power := Nat.pow_lt_pow_of_lt (a := 2) (by decide) small
    have shifted : (BitVec.ofNat 64 ((1 : Nat) <<< bits)).toNat = 2 ^ bits := by
      change ((1 : Nat) <<< bits) % 2 ^ 64 = 2 ^ bits
      rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.mod_eq_of_lt power]
    unfold lowMask
    simp only [full, ↓reduceIte]
    change (BitVec.ofNat 64 ((1 : Nat) <<< bits) - (1 : BitVec 64)).toNat = 2 ^ bits - 1
    rw [BitVec.toNat_sub_of_le]
    · rw [shifted, (show (1 : BitVec 64).toNat = 1 from rfl)]
    · rw [BitVec.le_def, shifted]
      change 1 ≤ 2 ^ bits
      exact Nat.two_pow_pos bits

theorem lowMask_bit (bits offset : Nat) (bounded : bits ≤ 64) :
    (lowMask bits).getLsbD offset = decide (offset < bits) := by
  rw [← BitVec.testBit_toNat, lowMask_toNat bits bounded, Nat.testBit_two_pow_sub_one]

theorem rangeWord_bit (position start stop offset : Nat) (inside : offset < 64) :
    (rangeWord position start stop).getLsbD offset =
      decide (start ≤ 64 * position + offset ∧ 64 * position + offset < stop) := by
  rw [rangeWord, BitVec.getLsbD_and, BitVec.getLsbD_not,
    lowMask_bit (min (stop - position * 64) 64) offset (Nat.min_le_right _ _),
    lowMask_bit (min (start - position * 64) 64) offset (Nat.min_le_right _ _)]
  simp only [inside, decide_true, Bool.true_and]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
  omega

/-- Overflowed source offsets are zero because physical input storage ends
strictly before the host sentinel. Redundant high zero limbs are unrestricted. -/
theorem shiftedWord_eq_native (index : NatOperand) (shift position : Nat)
    (physical : index.words.length < 2 ^ 64) :
    shiftedWord index shift position = NatShift.shiftedWord index shift position := by
  have words : ∀ i, NatShift.word index i = word index i := fun i => (word_eq index i).symm
  unfold shiftedWord NatShift.shiftedWord
  simp only [words, Nat.add_comm position (shift / 64)]
  by_cases safe : shift / 64 < 2 ^ 64 ∧ shift / 64 + position < 2 ^ 64
  · simp only [safe.1, safe.2, and_self, ↓reduceIte]
    by_cases aligned : shift % 64 = 0
    · simp [aligned]
    · simp only [aligned, ne_eq, not_false_eq_true, ↓reduceIte]
      by_cases next : shift / 64 + position + 1 < 2 ^ 64
      · simp [next]
      · simp only [next, ↓reduceIte]
        rw [word_past_storage index (shift / 64 + position + 1) (by omega)]
  · have past : index.words.length ≤ shift / 64 + position := by omega
    simp [safe, word_past_storage index _ past,
      word_past_storage index (shift / 64 + position + 1) (by omega)]

theorem shiftedWord_bit (index : NatOperand) (shift position offset : Nat)
    (physical : index.words.length < 2 ^ 64) (inside : offset < 64) :
    (shiftedWord index shift position).getLsbD offset =
      (index.value >>> shift).testBit (64 * position + offset) := by
  rw [shiftedWord_eq_native index shift position physical]
  exact NatShift.shiftedWord_bit index shift position offset inside

end SszNative.Indices

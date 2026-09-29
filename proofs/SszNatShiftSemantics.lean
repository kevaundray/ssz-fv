import SszNatShift

set_option autoImplicit false

namespace SszNative.NatShift

open NatArithmetic

/-- Bit observation of the original, possibly padded limb slice. -/
theorem limbs_testBit (words : List (BitVec 64)) (bit : Nat) :
    (Limbs.value words).testBit bit =
      (words[bit / 64]?.getD 0).getLsbD (bit % 64) := by
  induction words generalizing bit with
  | nil => simp [Limbs.value]
  | cons first rest ih =>
    rw [Limbs.value, Nat.add_comm,
      Nat.testBit_two_pow_mul_add (Limbs.value rest) first.isLt]
    by_cases low : bit < 64
    · simp [low, Nat.div_eq_of_lt low, Nat.mod_eq_of_lt low, BitVec.getLsbD]
    · have quotient : bit / 64 = (bit - 64) / 64 + 1 := by omega
      have remainder : bit % 64 = (bit - 64) % 64 := by omega
      simp only [low, ↓reduceIte, ih, quotient, List.getElem?_cons_succ, remainder]

theorem word_bit (operand : NatOperand) (index offset : Nat) (small : offset < 64) :
    (word operand index).getLsbD offset = operand.value.testBit (64 * index + offset) := by
  rw [NatOperand.value, limbs_testBit]
  have quotient : (64 * index + offset) / 64 = index := by omega
  have remainder : (64 * index + offset) % 64 = offset := by omega
  rw [quotient, remainder]
  rfl

theorem shiftedWord_bit (operand : NatOperand) (bits index offset : Nat)
    (small : offset < 64) :
    (shiftedWord operand bits index).getLsbD offset =
      (operand.value >>> bits).testBit (64 * index + offset) := by
  have shiftBits : bits % 64 < 64 := Nat.mod_lt _ (by decide)
  have decomposition := Nat.mod_add_div bits 64
  unfold shiftedWord
  by_cases zero : bits % 64 = 0
  · simp only [zero, ne_eq, not_true_eq_false, ↓reduceIte,
      BitVec.getLsbD_ushiftRight, Nat.zero_add, Nat.testBit_shiftRight]
    rw [word_bit operand _ offset small]
    congr 1
    omega
  · simp only [zero, ne_eq, not_false_eq_true, ↓reduceIte,
      BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_shiftLeft, small, decide_true, Bool.true_and,
      Nat.testBit_shiftRight]
    by_cases low : bits % 64 + offset < 64
    · have gap : offset < 64 - bits % 64 := by omega
      simp only [gap, decide_true, Bool.not_true, Bool.false_and, Bool.or_false]
      rw [word_bit operand _ _ low]
      congr 1
      omega
    · have gap : ¬ offset < 64 - bits % 64 := by omega
      rw [BitVec.getLsbD_of_ge _ _ (by omega : 64 ≤ bits % 64 + offset)]
      simp only [gap, decide_false, Bool.not_false, Bool.true_and, Bool.false_or]
      rw [word_bit operand _ _ (by omega)]
      congr 1
      omega

theorem leftWord_bit (operand : NatOperand) (bits index offset : Nat)
    (small : offset < 64) :
    (leftWord operand bits index).getLsbD offset =
      (operand.value <<< bits).testBit (64 * index + offset) := by
  have shiftBits : bits % 64 < 64 := Nat.mod_lt _ (by decide)
  have decomposition := Nat.mod_add_div bits 64
  by_cases before : index < bits / 64
  · have below : ¬ bits ≤ 64 * index + offset := by omega
    simp [leftWord, before, Nat.testBit_shiftLeft, below]
  · by_cases carry : bits % 64 ≠ 0 ∧ index - bits / 64 ≠ 0
    · have selected : leftWord operand bits index =
          (word operand (index - bits / 64) <<< (bits % 64)) |||
            (word operand (index - bits / 64 - 1) >>> (64 - bits % 64)) := by
        simp only [leftWord, before, ↓reduceIte]
        split
        · rfl
        · rename_i absent
          exact False.elim (absent carry)
      rw [selected, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
        BitVec.getLsbD_ushiftRight, Nat.testBit_shiftLeft]
      simp only [small, decide_true, Bool.true_and]
      have above : bits ≤ 64 * index + offset := by omega
      simp only [above, decide_true, Bool.true_and]
      by_cases low : offset < bits % 64
      · simp only [low, decide_true, Bool.not_true, Bool.false_and, Bool.false_or]
        rw [word_bit operand _ _ (by omega)]
        congr 1
        omega
      · simp only [low, decide_false, Bool.not_false, Bool.true_and]
        rw [BitVec.getLsbD_of_ge _ _ (by omega : 64 ≤ 64 - bits % 64 + offset),
          Bool.or_false, word_bit operand _ _ (by omega)]
        congr 1
        omega
    · have selected : leftWord operand bits index =
          word operand (index - bits / 64) <<< (bits % 64) := by
        simp only [leftWord, before, carry, ↓reduceIte]
      rw [selected, BitVec.getLsbD_shiftLeft, Nat.testBit_shiftLeft]
      simp only [small, decide_true, Bool.true_and]
      by_cases low : offset < bits % 64
      · have below : ¬ bits ≤ 64 * index + offset := by omega
        simp [low, below]
      · have above : bits ≤ 64 * index + offset := by omega
        simp only [low, decide_false, Bool.not_false, above, decide_true, Bool.true_and]
        rw [word_bit operand _ _ (by omega)]
        congr 1
        omega

/-- The width law is on the unrestricted mathematical natural. -/
theorem bitLength_le_iff (operand : NatOperand) (width : Nat) :
    bitLength operand ≤ width ↔ operand.value < 2^width := by
  by_cases zero : operand.value = 0
  · simp [bitLength, Serialize.bitLength, zero, Nat.two_pow_pos]
  · simp only [bitLength, Serialize.bitLength, zero, ↓reduceIte]
    have order : operand.value.log2 + 1 ≤ width ↔ operand.value.log2 < width := by omega
    exact order.trans (Nat.log2_lt zero)

theorem bitLength_zero_iff (operand : NatOperand) :
    bitLength operand = 0 ↔ operand.value = 0 := by
  have fits := bitLength_le_iff operand 0
  simpa using fits

theorem bit_false (operand : NatOperand) (index : Nat)
    (past : bitLength operand ≤ index) : operand.value.testBit index = false :=
  Nat.testBit_lt_two_pow ((bitLength_le_iff operand index).mp past)

theorem wordCount_covers (bits : Nat) : bits ≤ 64 * wordCount bits := by
  unfold wordCount
  omega

/-- Reconstruction needs only the proved per-limb bit observations and the
finite output width, not a postulated value of the execution. -/
theorem generated_value (count number : Nat) (generate : Nat → BitVec 64)
    (digits : ∀ index offset, offset < 64 →
      (generate index).getLsbD offset = number.testBit (64 * index + offset))
    (width : ∀ index, 64 * count ≤ index → number.testBit index = false) :
    Limbs.value (List.ofFn (fun i : Fin count => generate i.val)) = number := by
  apply Nat.eq_of_testBit_eq
  intro index
  rw [limbs_testBit, List.getElem?_ofFn]
  by_cases inside : index / 64 < count
  · simp only [inside, ↓reduceDIte, Option.getD_some]
    rw [digits _ _ (Nat.mod_lt _ (by decide))]
    congr 1
    omega
  · simp only [inside, ↓reduceDIte, Option.getD_none]
    change (0#64).getLsbD (index % 64) = number.testBit index
    rw [BitVec.getLsbD_zero]
    exact (width index (by omega)).symm

theorem leftWords_value (operand : NatOperand) (bits count : Nat)
    (enough : bitLength operand + bits ≤ 64 * count) :
    Limbs.value (List.ofFn (fun i : Fin count => leftWord operand bits i.val)) =
      operand.value <<< bits := by
  apply generated_value count _ _ (leftWord_bit operand bits)
  intro index past
  rw [Nat.testBit_shiftLeft]
  by_cases above : bits ≤ index
  · simp only [above, decide_true, Bool.true_and]
    exact bit_false operand _ (by omega)
  · simp [above]

theorem rightWords_value (operand : NatOperand) (bits count : Nat)
    (enough : bitLength operand - bits ≤ 64 * count) :
    Limbs.value (List.ofFn (fun i : Fin count => shiftedWord operand bits i.val)) =
      operand.value >>> bits := by
  apply generated_value count _ _ (shiftedWord_bit operand bits)
  intro index past
  rw [Nat.testBit_shiftRight]
  exact bit_false operand _ (by omega)

private theorem small_left_value (operand : NatOperand) (bits : Nat)
    (small : bitLength operand + bits ≤ 64) :
    (word operand 0 <<< bits).toNat = operand.value <<< bits := by
  apply Nat.eq_of_testBit_eq
  intro index
  rw [BitVec.testBit_toNat, BitVec.getLsbD_shiftLeft, Nat.testBit_shiftLeft]
  by_cases inside : index < 64
  · simp only [inside, decide_true, Bool.true_and]
    by_cases above : bits ≤ index
    · simp only [show ¬ index < bits by omega, decide_false, Bool.not_false,
        above, decide_true, Bool.true_and]
      simpa using word_bit operand 0 (index - bits) (by omega)
    · simp [above, show index < bits by omega]
  · simp only [inside, decide_false, Bool.false_and]
    by_cases above : bits ≤ index
    · simp only [above, decide_true, Bool.true_and]
      exact (bit_false operand _ (by omega)).symm
    · simp [above]

private theorem small_right_value (operand : NatOperand) (bits : Nat)
    (small : bitLength operand - bits ≤ 64) :
    (shiftedWord operand bits 0).toNat = operand.value >>> bits := by
  apply Nat.eq_of_testBit_eq
  intro index
  rw [BitVec.testBit_toNat]
  by_cases inside : index < 64
  · simpa using shiftedWord_bit operand bits 0 index inside
  · rw [BitVec.getLsbD_of_ge _ _ (by omega), Nat.testBit_shiftRight]
    exact (bit_false operand _ (by omega)).symm

theorem allocate_value (base capacity used count number : Nat) (generate : Nat → BitVec 64)
    (value : Limbs.value (List.ofFn (fun i : Fin count => generate i.val)) = number)
    (result : NatOperand)
    (success : (allocate base capacity used count generate).result = .ok result) :
    result.value = number := by
  unfold allocate at success
  split at success
  · cases success
  · cases success
    exact value

theorem shl_value (operand : NatOperand) (bits base capacity used : Nat) (result : NatOperand)
    (success : (shl operand bits base capacity used).result = .ok result) :
    result.value = operand.value <<< bits := by
  unfold shl at success
  dsimp only at success
  split at success
  · rename_i zero
    cases success
    change 0 = operand.value <<< bits
    rw [(bitLength_zero_iff operand).mp zero]
    simp
  · split at success
    · rename_i zero
      cases success
      simp [zero, NatOperand.normalized_value]
    · split at success
      · split at success
        · rename_i small
          cases success
          simpa [NatOperand.value, NatOperand.words, Limbs.value] using
            small_left_value operand bits small
        · split at success
          · split at success
            · exact allocate_value base capacity used _ _ _
                (leftWords_value operand bits _ (wordCount_covers _)) result success
            · cases success
          · cases success
      · cases success

theorem shr_value (operand : NatOperand) (bits base capacity used : Nat) (result : NatOperand)
    (success : (shr operand bits base capacity used).result = .ok result) :
    result.value = operand.value >>> bits := by
  unfold shr at success
  dsimp only at success
  split at success
  · rename_i past
    cases success
    have zero : operand.value >>> bits = 0 := by
      apply Nat.eq_of_testBit_eq
      intro index
      simp only [Nat.testBit_shiftRight, Nat.zero_testBit]
      exact bit_false operand _ (by omega)
    change 0 = operand.value >>> bits
    exact zero.symm
  · split at success
    · rename_i zero
      cases success
      simp [zero, NatOperand.normalized_value]
    · split at success
      · rename_i small
        cases success
        simpa [NatOperand.value, NatOperand.words, Limbs.value] using
          small_right_value operand bits small
      · exact allocate_value base capacity used _ _ _
          (rightWords_value operand bits _ (wordCount_covers _)) result success

/-- Only the physical representation is bounded; the logical value is not. -/
theorem bitLength_physical (operand : NatOperand) :
    bitLength operand ≤ 64 * operand.words.length :=
  (bitLength_le_iff operand _).mpr (Limbs.value_lt operand.words)

theorem bitLength_u128 (operand : NatOperand) (physical : operand.words.length < 2^64) :
    bitLength operand < 2^128 := by
  have := bitLength_physical operand
  omega

/-- All right-shift source offsets, including the extra zero-extended read,
fit usize for every actually initialized output word. -/
theorem shr_source_indices (operand : NatOperand) (bits index : Nat)
    (physical : operand.words.length < 2^64 - 1)
    (live : bits < bitLength operand)
    (indexBound : index < wordCount (bitLength operand - bits)) :
    bits / 64 < 2^64 ∧ index + bits / 64 < 2^64 ∧
      index + bits / 64 + 1 < 2^64 := by
  have := bitLength_physical operand
  unfold wordCount at indexBound
  omega

/-- Exact significant-prefix width expression used by native bit_len; the zero
case includes empty Large and arbitrarily many redundant zero limbs. -/
theorem bitLength_native (operand : NatOperand) :
    bitLength operand =
      if operand.wordCount = 0 then 0 else
        64 * (operand.wordCount - 1) +
          (word operand (operand.wordCount - 1)).toNat.log2 + 1 := by
  by_cases zero : operand.wordCount = 0
  · have empty : Limbs.trim operand.words = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa only [Limbs.trim_length, NatOperand.wordCount] using zero
    have valueZero := (Limbs.trim_eq_nil_iff_value_zero operand.words).mp empty
    simp [bitLength, Serialize.bitLength, NatOperand.value, valueZero, zero]
  · have positive : 0 < Limbs.sigWords operand.words := by
      change 0 < operand.wordCount
      omega
    simp only [zero, ↓reduceIte]
    exact Serialize.bitLength_significant operand.words positive

/-- The physical read-only operand contract supplies all machine-size bounds.
No bound on operand.value is assumed. -/
theorem physical_word_count (observe : Nat → Nat → Option Nat) (operand : NatOperand)
    (stored : operand.At observe) : operand.words.length < 2^64 - 1 := by
  cases operand with
  | small limb => simp [NatOperand.words]
  | large address limbs =>
    obtain ⟨positive, aligned, extent, reads⟩ := stored
    change limbs.length < 2^64 - 1
    omega

theorem shr_physical_indices (observe : Nat → Nat → Option Nat) (operand : NatOperand)
    (stored : operand.At observe) (bits index : Nat)
    (live : bits < bitLength operand)
    (indexBound : index < wordCount (bitLength operand - bits)) :
    bits / 64 < 2^64 ∧ index + bits / 64 < 2^64 ∧
      index + bits / 64 + 1 < 2^64 :=
  shr_source_indices operand bits index (physical_word_count observe operand stored) live indexBound

theorem shr_physical_count (observe : Nat → Nat → Option Nat) (operand : NatOperand)
    (stored : operand.At observe) (bits : Nat)
    (live : bits < bitLength operand) :
    wordCount (bitLength operand - bits) < 2^64 := by
  have := physical_word_count observe operand stored
  have := bitLength_physical operand
  unfold wordCount
  omega

end SszNative.NatShift

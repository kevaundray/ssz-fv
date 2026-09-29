import SszIndicesArithmeticPower
import SszNatNarrow
import Init.Data.Nat.Power2.Lemmas

set_option autoImplicit false

namespace SszNative.Indices

/-- The wrapping predecessor is used only after the nonzero test. -/
theorem wordPowerOfTwo_iff (value : BitVec 64) :
    wordPowerOfTwo value = true ↔ Nat.isPowerOfTwo value.toNat := by
  by_cases zero : value = 0
  · simp [wordPowerOfTwo, zero, Nat.not_isPowerOfTwo_zero]
  · have nonzero : value.toNat ≠ 0 := by
      intro h
      apply zero
      apply BitVec.eq_of_toNat_eq
      simpa using h
    have predecessor : (value - 1).toNat = value.toNat - 1 := by
      apply BitVec.toNat_sub_of_le
      change 1 ≤ value.toNat
      omega
    simp only [wordPowerOfTwo, Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
    change (value ≠ 0 ∧ (value &&& (value - 1)) = 0) ↔
      Nat.isPowerOfTwo value.toNat
    constructor
    · intro accepted
      have natural := congrArg BitVec.toNat accepted.2
      change value.toNat &&& (value - 1).toNat = 0 at natural
      rw [predecessor] at natural
      exact (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo nonzero).mp natural
    · intro power
      refine ⟨zero, BitVec.eq_of_toNat_eq ?_⟩
      change value.toNat &&& (value - 1).toNat = 0
      rw [predecessor]
      exact (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo nonzero).mpr power

/-- A power has exactly one nonzero radix digit, and that digit is a power. -/
theorem radix_power_iff (low high : Nat) (bound : low < 2 ^ 64) :
    Nat.isPowerOfTwo (low + 2 ^ 64 * high) ↔
      if low = 0 then Nat.isPowerOfTwo high
      else Nat.isPowerOfTwo low ∧ high = 0 := by
  constructor
  · rintro ⟨exponent, equal⟩
    by_cases small : exponent < 64
    · have powerBound : 2 ^ exponent < 2 ^ 64 :=
        (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr small
      have highZero : high = 0 := by omega
      have lowPower : low = 2 ^ exponent := by simpa [highZero] using equal
      have nonzero : low ≠ 0 := by rw [lowPower]; exact Nat.ne_of_gt (Nat.two_pow_pos _)
      simp only [nonzero, ↓reduceIte]
      exact ⟨⟨exponent, lowPower⟩, highZero⟩
    · have factor : 2 ^ exponent = 2 ^ 64 * 2 ^ (exponent - 64) := by
        rw [← Nat.pow_add, Nat.add_sub_of_le (by omega : 64 ≤ exponent)]
      rw [factor] at equal
      have lowZero : low = 0 := by omega
      have highPower : high = 2 ^ (exponent - 64) := by omega
      simp only [lowZero, ↓reduceIte]
      exact ⟨exponent - 64, highPower⟩
  · split
    · rename_i zero
      rintro ⟨exponent, equal⟩
      refine ⟨64 + exponent, ?_⟩
      simp [zero, equal, Nat.pow_add]
    · rintro ⟨⟨exponent, equal⟩, zero⟩
      exact ⟨exponent, by simpa [zero] using equal⟩

/-- Logical meaning of a scan over any supplied finite window. The `seen`
flag is an already accepted power limb, so only zero limbs may follow it. -/
theorem powerScan_window (index : NatOperand) (words : List (BitVec 64))
    (position : Nat) (seen : Bool)
    (observed : ∀ offset, offset < words.length →
      word index (position + offset) = words[offset]?.getD 0) :
    powerScan index position words.length seen = true ↔
      if seen then Limbs.value words = 0 else Nat.isPowerOfTwo (Limbs.value words) := by
  induction words generalizing position seen with
  | nil => cases seen <;> simp [powerScan, Limbs.value, Nat.not_isPowerOfTwo_zero]
  | cons first rest ih =>
      have firstWord : word index position = first := by
        simpa using observed 0 (by simp)
      have restWords : ∀ offset, offset < rest.length →
          word index (position + 1 + offset) = rest[offset]?.getD 0 := by
        intro offset inside
        simpa only [List.getElem?_cons_succ, Nat.add_assoc, Nat.add_comm 1 offset]
          using observed (offset + 1) (by simp; omega)
      have next := ih (position + 1) true restWords
      have same := ih (position + 1) seen restWords
      have firstZero : first = 0 ↔ first.toNat = 0 := by
        simpa using (BitVec.toNat_eq (x := first) (y := 0))
      have meaning := radix_power_iff first.toNat (Limbs.value rest) first.isLt
      by_cases zero : first = 0
      · have zeroMeaning :
            Nat.isPowerOfTwo (2 ^ 64 * Limbs.value rest) ↔
              Nat.isPowerOfTwo (Limbs.value rest) := by
          simpa using radix_power_iff 0 (Limbs.value rest) (by decide)
        cases seen with
        | false =>
            simpa [powerScan, firstWord, zero, Limbs.value, zeroMeaning] using same
        | true =>
            simpa [powerScan, firstWord, zero, Limbs.value, Nat.mul_eq_zero] using same
      · have nz : first.toNat ≠ 0 := fun h => zero (firstZero.mpr h)
        change first ≠ 0#64 at zero
        cases seen with
        | true =>
            simp [powerScan, firstWord, zero, Limbs.value, nz]
        | false =>
            by_cases power : wordPowerOfTwo first = true
            · have logical := (wordPowerOfTwo_iff first).mp power
              simpa [powerScan, firstWord, zero, power, Limbs.value, meaning, nz, logical]
                using next
            · have logical : ¬ Nat.isPowerOfTwo first.toNat := by
                intro h
                exact power ((wordPowerOfTwo_iff first).mpr h)
              simp [powerScan, firstWord, zero, power, Limbs.value, meaning, nz, logical]

/-- Significant-prefix scanning is exact for every raw representation, including
empty Large operands and arbitrarily many redundant high zero limbs. -/
theorem powerOfTwo_iff (index : NatOperand) :
    powerOfTwo index = true ↔ ∃ exponent : Nat, index.value = 2 ^ exponent := by
  have selected : Limbs.value (index.words.take index.wordCount) = index.value := by
    simpa only [NatOperand.wordCount, NatOperand.value, Limbs.sigWords, List.take_length]
      using Serialize.significant_prefix_value index.words index.words.length
  have count : (index.words.take index.wordCount).length = index.wordCount := by
    rw [List.length_take, NatOperand.wordCount,
      Nat.min_eq_left (Limbs.sigWords_le_length index.words)]
  have scan := powerScan_window index (index.words.take index.wordCount) 0 false
    (by
      intro offset inside
      have within : offset < index.wordCount := by rw [count] at inside; exact inside
      simp [word_eq, within])
  simpa only [count, Bool.false_eq_true, ↓reduceIte, selected, powerOfTwo,
    Nat.isPowerOfTwo] using scan

theorem powerOfTwo_log2_iff (index : NatOperand) :
    powerOfTwo index = true ↔ index.value = 2 ^ index.value.log2 := by
  rw [powerOfTwo_iff]
  constructor
  · rintro ⟨exponent, equal⟩
    rw [equal, Nat.log2_two_pow]
  · intro equal
    exact ⟨index.value.log2, equal⟩

theorem powerOfTwo_value_congr (left right : NatOperand)
    (equal : left.value = right.value) : powerOfTwo left = powerOfTwo right := by
  apply Bool.eq_iff_iff.mpr
  rw [powerOfTwo_iff, powerOfTwo_iff, equal]

/-- Significant one-word values are independent of redundant physical padding. -/
theorem word_zero_value_of_fits (width : NatOperand) (fits : width.wordCount ≤ 1) :
    (word width 0).toNat = width.value := by
  have small := (width.wordCount_le_iff_value_lt 1).mp fits
  have low : Limbs.value width.words % 2 ^ 64 = (word width 0).toNat := by
    rw [word_eq]
    cases width.words with
    | nil => simp [Limbs.value]
    | cons first rest => simp [Limbs.value, Nat.mod_eq_of_lt first.isLt]
  exact low.symm.trans (Nat.mod_eq_of_lt small)

/-- Small-word guards inspect significant width, not the raw slice length. -/
theorem one_word_le_iff (index : NatOperand) (bound : Nat) (small : bound < 2 ^ 64) :
    (index.wordCount ≤ 1 ∧ (word index 0).toNat ≤ bound) ↔ index.value ≤ bound := by
  constructor
  · rintro ⟨fits, below⟩
    rwa [word_zero_value_of_fits index fits] at below
  · intro below
    have fits : index.wordCount ≤ 1 :=
      (index.wordCount_le_iff_value_lt 1).mpr (by omega)
    exact ⟨fits, by rwa [word_zero_value_of_fits index fits]⟩

/-- Packing recognizes the complete six-width fast-path domain. -/
theorem packingShift_spec (width : NatOperand) (shift : Nat)
    (success : packingShift width = some shift) :
    shift ≤ 5 ∧ width.value = 2 ^ (5 - shift) := by
  unfold packingShift at success
  split at success
  next fits =>
    dsimp only at success
    split at success
    next accepted =>
      have wordValue := word_zero_value_of_fits width fits
      obtain ⟨exponent, power⟩ := (wordPowerOfTwo_iff _).mp accepted.2
      have exponentBound : exponent ≤ 5 := by
        have hp : 2 ^ exponent ≤ 2 ^ 5 := by simpa [power] using accepted.1
        exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp
      have result : shift = 5 - exponent := by
        simpa only [power, Nat.log2_two_pow, Option.some.injEq] using success.symm
      refine ⟨by omega, ?_⟩
      rw [← wordValue, power, result, Nat.sub_sub_self exponentBound]
    next rejected => simp at success
  next wide => simp at success

theorem packingShift_iff (width : NatOperand) (shift : Nat) :
    packingShift width = some shift ↔ shift ≤ 5 ∧ width.value = 2 ^ (5 - shift) := by
  constructor
  · exact packingShift_spec width shift
  · rintro ⟨bound, value⟩
    have small : width.value ≤ 32 := by
      rw [value]
      exact Nat.pow_le_pow_right (by decide) (Nat.sub_le 5 shift)
    have fits : width.wordCount ≤ 1 :=
      (width.wordCount_le_iff_value_lt 1).mpr (by omega)
    have wordValue := word_zero_value_of_fits width fits
    have power : wordPowerOfTwo (word width 0) = true :=
      (wordPowerOfTwo_iff _).mpr ⟨5 - shift, wordValue.trans value⟩
    have accepted : (word width 0).toNat ≤ 32 ∧ wordPowerOfTwo (word width 0) = true :=
      ⟨by rw [wordValue]; exact small, power⟩
    unfold packingShift
    simp only [fits, ↓reduceIte]
    simp only [accepted, and_self, ↓reduceIte]
    rw [wordValue, value, Nat.log2_two_pow, Nat.sub_sub_self bound]

theorem packed_width_identity (width : NatOperand) (shift : Nat)
    (success : packingShift width = some shift) :
    2 ^ shift * width.value = 32 := by
  obtain ⟨bound, value⟩ := packingShift_spec width shift success
  rw [value, ← Nat.pow_add, Nat.add_sub_of_le bound]

/-- These identities use only the six accepted widths, not a bound on `number`. -/
theorem packed_div_identity (number : Nat) (width : NatOperand) (shift : Nat)
    (success : packingShift width = some shift) :
    number / 2 ^ shift = number * width.value / 32 := by
  obtain ⟨bound, value⟩ := packingShift_spec width shift success
  rw [value]
  have choices : shift = 0 ∨ shift = 1 ∨ shift = 2 ∨ shift = 3 ∨ shift = 4 ∨ shift = 5 := by omega
  rcases choices with h | h | h | h | h | h <;> subst shift <;> simp only [Nat.reduceSub, Nat.reducePow] <;> omega

theorem packed_ceil_identity (number : Nat) (width : NatOperand) (shift : Nat)
    (success : packingShift width = some shift) :
    (number * width.value + 31) / 32 = (number + 2 ^ shift - 1) / 2 ^ shift := by
  obtain ⟨bound, value⟩ := packingShift_spec width shift success
  rw [value]
  have choices : shift = 0 ∨ shift = 1 ∨ shift = 2 ∨ shift = 3 ∨ shift = 4 ∨ shift = 5 := by omega
  rcases choices with h | h | h | h | h | h <;> subst shift <;> simp only [Nat.reduceSub, Nat.reducePow] <;> omega

end SszNative.Indices

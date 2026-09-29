import SszProofTraversal
import SszIndicesArithmeticSemanticWords
import SszMerkleAccumulatorDepth
import SszIndicesPowerSemantic

set_option autoImplicit false

namespace SszNative.Proof

/-- Checked source-word conversions agree with the shared borrowed view. -/
theorem shiftedWord_eq_indices (index : NatOperand) (offset position : Nat) :
    shiftedWord index offset position = Indices.shiftedWord index offset position := by
  unfold shiftedWord Indices.shiftedWord physicalIndex
  by_cases source : offset / 64 + position < 2 ^ 64
  · have base : offset / 64 < 2 ^ 64 := by omega
    simp only [source, base, and_self, ↓reduceIte]
    by_cases zero : offset % 64 = 0
    · simp [zero]
    · by_cases next : offset / 64 + position + 1 < 2 ^ 64
      · simp only [zero, next, ↓reduceIte]
      · simp only [zero, next, ↓reduceIte]
  · have high : ¬offset / 64 + position + 1 < 2 ^ 64 := by omega
    simp [source, high]

private theorem value_lt_bitLength (index : NatOperand) :
    index.value < 2 ^ Indices.bitLength index := by
  rw [Indices.bitLength_value]
  change index.value < 2 ^ MerkleAccumulator.bitLength index.value
  exact (MerkleAccumulator.bitLength_le_iff _ _).mp (Nat.le_refl _)

private theorem bit_above_length (index : NatOperand) (position : Nat)
    (above : Indices.bitLength index ≤ position) : index.value.testBit position = false := by
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (value_lt_bitLength index)
    (Nat.pow_le_pow_right (by decide) above))

/-- Removing bits beyond the source's significant width preserves every requested
bit, even when either logical offset or logical width exceeds a machine word. -/
theorem window_effective_value (index : NatOperand) (offset width : Nat) :
    (index.value / 2 ^ offset) % 2 ^ min (Indices.bitLength index - offset) width =
      (index.value / 2 ^ offset) % 2 ^ width := by
  apply Nat.eq_of_testBit_eq
  intro bit
  simp only [Nat.testBit_mod_two_pow, ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
  by_cases inside : bit < Indices.bitLength index - offset
  · simp [Nat.lt_min, inside]
  · have clear := bit_above_length index (offset + bit) (by omega)
    simp [clear]

private theorem windowHighZero_iff (index : NatOperand) (offset effective position count : Nat) :
    windowHighZero index offset effective position count = true ↔
      ∀ p, position ≤ p → p < position + count →
        shiftedWord index offset p &&& windowMask (min (effective - p * 64) 64) = 0 := by
  induction count generalizing position with
  | zero =>
      constructor
      · intro _ p lower upper
        omega
      · intro _
        rfl
  | succ count ih =>
      simp only [windowHighZero]
      by_cases clear : shiftedWord index offset position &&&
          windowMask (min (effective - position * 64) 64) = 0
      · simp only [clear, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ih]
        constructor
        · intro rest p lower upper
          by_cases first : p = position
          · simpa [first] using clear
          · exact rest p (by omega) (by omega)
        · intro every p lower upper
          exact every p (by omega) (by omega)
      · have nonzero : (shiftedWord index offset position &&&
            windowMask (min (effective - position * 64) 64) != 0) = true :=
          bne_iff_ne.mpr clear
        simp only [nonzero, ↓reduceIte, Bool.false_eq_true]
        constructor
        · intro impossible
          cases impossible
        · intro every
          exact clear (every position (by omega) (by omega))

private theorem effective_words_physical (index : NatOperand) (offset width : Nat)
    (physical : index.words.length < 2 ^ 64) :
    (min (Indices.bitLength index - offset) width + 63) / 64 < 2 ^ 64 := by
  have storage := Indices.bitLength_le_storage index
  have effective := Nat.min_le_left (Indices.bitLength index - offset) width
  omega

private theorem maskedWord_bit (index : NatOperand) (offset position held bit : Nat)
    (physical : index.words.length < 2 ^ 64) (inside : bit < 64) :
    (shiftedWord index offset position &&& windowMask held).getLsbD bit =
      (decide (bit < held) && index.value.testBit (offset + (64 * position + bit))) := by
  have mask : windowMask held = BitVec.ofNat 64 (2 ^ held - 1) := by
    unfold windowMask
    split <;> simp_all
  rw [BitVec.getLsbD_and, shiftedWord_eq_indices,
    Indices.shiftedWord_bit index offset position bit physical inside, mask,
    BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight]
  simp only [inside, decide_true, Bool.true_and, Bool.and_comm]

private theorem maskedWord_zero_iff (index : NatOperand) (offset position held : Nat)
    (physical : index.words.length < 2 ^ 64) (bounded : held ≤ 64) :
    shiftedWord index offset position &&& windowMask held = 0 ↔
      ∀ bit, bit < held → index.value.testBit (offset + (64 * position + bit)) = false := by
  constructor
  · intro zero bit inside
    have observed := congrArg (fun word : BitVec 64 => word.getLsbD bit) zero
    simpa [maskedWord_bit index offset position held bit physical (by omega), inside]
      using observed
  · intro clear
    apply BitVec.eq_of_getLsbD_eq
    intro bit inside
    rw [maskedWord_bit index offset position held bit physical inside]
    by_cases heldBit : bit < held
    · simp [heldBit, clear bit heldBit]
    · simp [heldBit]

private theorem highZero_iff_bits (index : NatOperand) (offset effective : Nat)
    (physical : index.words.length < 2 ^ 64) :
    windowHighZero index offset effective 1 ((effective + 63) / 64 - 1) = true ↔
      ∀ bit, 64 ≤ bit → bit < effective → index.value.testBit (offset + bit) = false := by
  rw [windowHighZero_iff]
  constructor
  · intro clear bit lower upper
    have pLower : 1 ≤ bit / 64 := by omega
    have pUpper : bit / 64 < 1 + ((effective + 63) / 64 - 1) := by omega
    have selected := (maskedWord_zero_iff index offset (bit / 64)
      (min (effective - bit / 64 * 64) 64) physical (Nat.min_le_right _ _)).mp
      (clear (bit / 64) pLower pUpper) (bit % 64) (by omega)
    simpa only [show 64 * (bit / 64) + bit % 64 = bit by omega] using selected
  · intro clear p lower upper
    apply (maskedWord_zero_iff index offset p (min (effective - p * 64) 64)
      physical (Nat.min_le_right _ _)).mpr
    intro bit inside
    exact clear (64 * p + bit) (by omega) (by omega)

private theorem highZero_iff_fits (index : NatOperand) (offset effective : Nat)
    (physical : index.words.length < 2 ^ 64) :
    windowHighZero index offset effective 1 ((effective + 63) / 64 - 1) = true ↔
      (index.value / 2 ^ offset) % 2 ^ effective < 2 ^ 64 := by
  rw [highZero_iff_bits index offset effective physical]
  constructor
  · intro clear
    apply Nat.lt_pow_two_of_testBit
    intro bit lower
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    by_cases inside : bit < effective
    · simp [inside, clear bit lower inside, Nat.add_comm]
    · simp [inside]
  · intro fits bit lower inside
    have zero := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le fits
      (Nat.pow_le_pow_right (by decide) lower))
    simpa [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, inside, Nat.add_comm] using zero

private theorem lowWord_value (index : NatOperand) (offset effective : Nat)
    (physical : index.words.length < 2 ^ 64) :
    (shiftedWord index offset 0 &&&
      (if 64 ≤ effective then windowMask 64 else windowMask effective)).toNat =
      ((index.value / 2 ^ offset) % 2 ^ effective) % 2 ^ 64 := by
  apply Nat.eq_of_testBit_eq
  intro bit
  -- Expose both modulus bits before literal reduction can hide the powers of two.
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases inside : bit < 64
  · simp only [inside, decide_true, Bool.true_and]
    rw [BitVec.testBit_toNat]
    by_cases full : 64 ≤ effective
    · simp only [full, ↓reduceIte]
      rw [maskedWord_bit index offset 0 64 bit physical inside]
      simp only [Nat.mul_zero, Nat.zero_add]
      simp only [inside, Nat.lt_of_lt_of_le inside full, decide_true,
        Bool.true_and, Nat.add_comm bit offset]
    · simp only [full, ↓reduceIte]
      rw [maskedWord_bit index offset 0 effective bit physical inside]
      simp only [Nat.mul_zero, Nat.zero_add]
      rw [Nat.add_comm bit offset]
  · have zero := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le
      (shiftedWord index offset 0 &&&
        (if 64 ≤ effective then windowMask 64 else windowMask effective)).isLt
      (Nat.pow_le_pow_right (by decide) (by omega : 64 ≤ bit)))
    simp only [zero, inside, decide_false, Bool.false_and]

/-- Exact native window semantics. Only physical source storage is bounded;
the represented natural, requested offset, and requested width remain arbitrary. -/
theorem window_eq (index : NatOperand) (offset width : Nat)
    (physical : index.words.length < 2 ^ 64) :
    window index offset width =
      if (index.value / 2 ^ offset) % 2 ^ width < 2 ^ 64
      then some ((index.value / 2 ^ offset) % 2 ^ width) else none := by
  let effective := min (Indices.bitLength index - offset) width
  have truncation := window_effective_value index offset width
  change (index.value / 2 ^ offset) % 2 ^ effective =
    (index.value / 2 ^ offset) % 2 ^ width at truncation
  unfold window
  change (if effective = 0 then some 0 else
    match physicalIndex ((effective + 63) / 64) with
    | none => none
    | some words =>
        if windowHighZero index offset effective 1 (words - 1) then
          physicalIndex (shiftedWord index offset 0 &&&
            (if 64 ≤ effective then windowMask 64 else windowMask effective)).toNat
        else none) = _
  rw [← truncation]
  by_cases empty : effective = 0
  · simp only [empty, Nat.pow_zero, Nat.mod_one, Nat.two_pow_pos, ↓reduceIte]
  · simp only [empty, ↓reduceIte]
    have wordsPhysical : (effective + 63) / 64 < 2 ^ 64 :=
      effective_words_physical index offset width physical
    rw [physicalIndex_of_lt _ wordsPhysical]
    change (if windowHighZero index offset effective 1 ((effective + 63) / 64 - 1) then
      physicalIndex (shiftedWord index offset 0 &&&
        (if 64 ≤ effective then windowMask 64 else windowMask effective)).toNat
      else none) =
        if (index.value / 2 ^ offset) % 2 ^ effective < 2 ^ 64
        then some ((index.value / 2 ^ offset) % 2 ^ effective) else none
    by_cases fits : (index.value / 2 ^ offset) % 2 ^ effective < 2 ^ 64
    · have scan := (highZero_iff_fits index offset effective physical).mpr fits
      simp only [scan, ↓reduceIte]
      rw [lowWord_value index offset effective physical,
        Nat.mod_eq_of_lt fits, physicalIndex_of_lt _ fits]
      simp only [fits, ↓reduceIte]
    · have scan : windowHighZero index offset effective 1 ((effective + 63) / 64 - 1) ≠ true :=
        fun scan => fits ((highZero_iff_fits index offset effective physical).mp scan)
      simp only [scan, fits, Bool.false_eq_true, ↓reduceIte]


/-- Successful truncation returns the complete window, not merely its low limb. -/
theorem window_of_fits (index : NatOperand) (offset width : Nat)
    (physical : index.words.length < 2 ^ 64)
    (fits : (index.value / 2 ^ offset) % 2 ^ width < 2 ^ 64) :
    window index offset width = some ((index.value / 2 ^ offset) % 2 ^ width) := by
  simp only [window_eq index offset width physical, fits, ↓reduceIte]

/-- A significant high window limb denotes an absent physical position. -/
theorem window_of_oversized (index : NatOperand) (offset width : Nat)
    (physical : index.words.length < 2 ^ 64)
    (oversized : 2 ^ 64 ≤ (index.value / 2 ^ offset) % 2 ^ width) :
    window index offset width = none := by
  simp only [window_eq index offset width physical, Nat.not_lt.mpr oversized, ↓reduceIte]

theorem ceilDepth_eq_capacityDepth (capacity : NatOperand) :
    ceilDepth capacity = MerkleAccumulator.capacityDepth capacity := by
  unfold ceilDepth
  rw [Indices.bitLength_value]
  change (if MerkleAccumulator.bitLength capacity.value = 0 then 0
    else if Indices.powerOfTwo capacity then MerkleAccumulator.bitLength capacity.value - 1
    else MerkleAccumulator.bitLength capacity.value) = _
  simp only [Indices.powerOfTwo_log2_iff]
  unfold MerkleAccumulator.capacityDepth
  by_cases empty : MerkleAccumulator.bitLength capacity.value = 0
  · simp only [empty, ↓reduceIte, Nat.zero_sub]
  · simp only [empty, ↓reduceIte]
    -- Split the power test rather than rewriting the value inside its own log2.
    split <;> rfl

/-- Native significant-bit and single-set-bit scans compute the pinned rounded
tree depth for every raw capacity, including zero and noncanonical Large values. -/
theorem ceilDepth_eq_log2_nextPow2 (capacity : NatOperand) :
    ceilDepth capacity = (Ssz.nextPow2 capacity.value).log2 := by
  rw [ceilDepth_eq_capacityDepth, MerkleAccumulator.capacityDepth_eq_depthFor,
    Ssz.nextPow2, Nat.log2_two_pow]

end SszNative.Proof

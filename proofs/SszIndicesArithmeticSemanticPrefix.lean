import SszIndicesArithmeticSemanticShift

set_option autoImplicit false

namespace SszNative.Indices

theorem prefixFlipDomain_of_nonroot (index : NatOperand) (shift : Nat) (flip : Bool)
    (nonroot : 1 < index.value >>> shift) : PrefixFlipDomain index shift flip := by
  intro flipped
  by_cases wide : 1 < bitLength index - shift
  · exact wide
  · have bounded : index.value >>> shift < 2 ^ 1 := by
      apply Nat.lt_pow_two_of_testBit
      intro position past
      exact shifted_bit_false index shift position (by omega)
    omega

theorem shifted_bit_top (index : NatOperand) (shift : Nat)
    (positive : 0 < bitLength index - shift) :
    (index.value >>> shift).testBit (bitLength index - shift - 1) = true := by
  have nonzero : index.value ≠ 0 := by
    intro zero
    simp [bitLength_value, Serialize.bitLength, zero] at positive
  have width : bitLength index = index.value.log2 + 1 := by
    simp [bitLength_value, Serialize.bitLength, nonzero]
  rw [Nat.testBit_shiftRight,
    show shift + (bitLength index - shift - 1) = index.value.log2 by omega]
  exact Nat.testBit_log2 nonzero

theorem prefix_bit_false (index : NatOperand) (shift : Nat) (flip : Bool)
    (domain : PrefixFlipDomain index shift flip) (position : Nat)
    (past : bitLength index - shift ≤ position) :
    ((index.value >>> shift) ^^^ (if flip then 1 else 0)).testBit position = false := by
  rw [Nat.testBit_xor, shifted_bit_false index shift position past]
  cases flip with
  | false => simp
  | true =>
      have large := domain rfl
      have nonzero : position ≠ 0 := by omega
      simp [one_bit, nonzero]

theorem prefix_bit_top (index : NatOperand) (shift : Nat) (flip : Bool)
    (domain : PrefixFlipDomain index shift flip) (positive : 0 < bitLength index - shift) :
    ((index.value >>> shift) ^^^ (if flip then 1 else 0)).testBit
      (bitLength index - shift - 1) = true := by
  rw [Nat.testBit_xor, shifted_bit_top index shift positive]
  cases flip with
  | false => simp
  | true =>
      have large := domain rfl
      have nonzero : bitLength index - shift - 1 ≠ 0 := by omega
      simp [one_bit, nonzero]

theorem prefix_width_eq (left : NatOperand) (leftShift : Nat) (flip : Bool)
    (right : NatOperand) (rightShift : Nat) (domain : PrefixFlipDomain left leftShift flip)
    (same : ((left.value >>> leftShift) ^^^ (if flip then 1 else 0)) =
      right.value >>> rightShift) :
    bitLength left - leftShift = bitLength right - rightShift := by
  by_cases equal : bitLength left - leftShift = bitLength right - rightShift
  · exact equal
  · by_cases less : bitLength left - leftShift < bitLength right - rightShift
    · have top := shifted_bit_top right rightShift (by omega)
      have empty := prefix_bit_false left leftShift flip domain
        (bitLength right - rightShift - 1) (by omega)
      rw [same, top] at empty
      contradiction
    · have top := prefix_bit_top left leftShift flip domain (by omega)
      have empty := shifted_bit_false right rightShift
        (bitLength left - leftShift - 1) (by omega)
      rw [same, empty] at top
      contradiction

theorem prefix_word_count (index : NatOperand) (shift : Nat)
    (physical : index.words.length < 2 ^ 64) :
    (bitLength index - shift) / 64 +
      (if (bitLength index - shift) % 64 = 0 then 0 else 1) < 2 ^ 64 := by
  have bounded := bitLength_le_storage index
  split <;> omega

/-- The source width precheck is sound exactly on the non-root flip domain.
For flip=false there is no nonzero, canonicality, or generalized-index premise. -/
theorem prefixEqual_refines (left : NatOperand) (leftShift : Nat) (flip : Bool)
    (right : NatOperand) (rightShift : Nat)
    (leftPhysical : left.words.length < 2 ^ 64)
    (rightPhysical : right.words.length < 2 ^ 64)
    (domain : PrefixFlipDomain left leftShift flip) :
    prefixEqual left leftShift flip right rightShift =
      decide (((left.value >>> leftShift) ^^^ (if flip then 1 else 0)) =
        right.value >>> rightShift) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  let bits := bitLength left - leftShift
  let count := bits / 64 + if bits % 64 = 0 then 0 else 1
  have countSmall : count < 2 ^ 64 := prefix_word_count left leftShift leftPhysical
  have covers : bits ≤ 64 * count := by
    dsimp only [count]
    split <;> omega
  constructor
  · intro compared
    have widths : bitLength left - leftShift = bitLength right - rightShift := by
      by_cases equal : bitLength left - leftShift = bitLength right - rightShift
      · exact equal
      · simp [prefixEqual, equal] at compared
    have gate : (bitLength left - leftShift != bitLength right - rightShift) = false := by
      simp [widths]
    have each : ∀ i, i < count →
        shiftedWord left leftShift i ^^^ (if flip && i == 0 then 1 else 0) =
          shiftedWord right rightShift i := by
      have scanned : allWords (fun i =>
          (shiftedWord left leftShift i ^^^ (if flip && i == 0 then 1 else 0)) ==
            shiftedWord right rightShift i) count = true := by
        have modulus :
            ((bitLength left - leftShift) / 64 +
              (if (bitLength left - leftShift) % 64 = 0 then 0 else 1)) % 2 ^ 64 = count :=
          Nat.mod_eq_of_lt countSmall
        simpa only [prefixEqual, gate, Bool.false_eq_true, ↓reduceIte, modulus] using compared
      intro i inside
      simpa only [beq_iff_eq] using ((allWords_iff _ count).mp scanned i inside)
    apply Nat.eq_of_testBit_eq
    intro position
    by_cases inside : position < 64 * count
    · have digit := congrArg (fun value : BitVec 64 => value.getLsbD (position % 64))
        (each (position / 64) (by omega))
      rw [xorWord_bit left leftShift flip _ _ leftPhysical (Nat.mod_lt _ (by decide)),
        shiftedWord_bit right rightShift _ _ rightPhysical (Nat.mod_lt _ (by decide))] at digit
      rw [show 64 * (position / 64) + position % 64 = position by omega] at digit
      exact digit
    · rw [prefix_bit_false left leftShift flip domain position (by dsimp [bits] at covers; omega),
        shifted_bit_false right rightShift position (by dsimp [bits] at covers; omega)]
  · intro same
    have widths := prefix_width_eq left leftShift flip right rightShift domain same
    have gate : (bitLength left - leftShift != bitLength right - rightShift) = false := by
      simp [widths]
    have scanned : allWords (fun i =>
        (shiftedWord left leftShift i ^^^ (if flip && i == 0 then 1 else 0)) ==
          shiftedWord right rightShift i) count = true := by
      apply (allWords_iff _ count).mpr
      intro position inside
      apply beq_iff_eq.mpr
      apply BitVec.eq_of_getLsbD_eq
      intro offset small
      rw [xorWord_bit left leftShift flip position offset leftPhysical small,
        shiftedWord_bit right rightShift position offset rightPhysical small, same]
    have modulus :
        ((bitLength left - leftShift) / 64 +
          (if (bitLength left - leftShift) % 64 = 0 then 0 else 1)) % 2 ^ 64 = count :=
      Nat.mod_eq_of_lt countSmall
    simpa only [prefixEqual, gate, Bool.false_eq_true, ↓reduceIte, modulus] using scanned

/-- Root xor is a real excluded case, not a generalized-index validation error. -/
theorem prefixEqual_root_zero_counterexample :
    prefixEqual (.small 1) 0 true (.small 0) 0 = false ∧
      (((1 : Nat) >>> 0) ^^^ 1) = (0 : Nat) := by
  decide

/-- Flipping an empty prefix is also outside the comparator's domain. -/
theorem prefixEqual_empty_flip_counterexample :
    prefixEqual (.large 0 []) 0 true (.large 0 []) 0 = true ∧
      (((0 : Nat) >>> 0) ^^^ 1) ≠ (0 : Nat) := by
  decide

end SszNative.Indices

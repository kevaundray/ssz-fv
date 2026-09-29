import SszIndicesArithmeticSemanticPrefix

set_option autoImplicit false

namespace SszX86.IndicesPrefixEqual
open SszNative SszNative.Indices

/-- The linked loop visits low words first; the shared model visits high words
first. Both short-circuit scans observe exactly the same borrowed words. -/
def scanWords (predicate : Nat → Bool) (first : Nat) : Nat → Bool
  | 0 => true
  | remaining + 1 => predicate first && scanWords predicate (first + 1) remaining

theorem scanWords_iff (predicate : Nat → Bool) (first count : Nat) :
    scanWords predicate first count = true ↔
      ∀ i, i < count → predicate (first + i) = true := by
  induction count generalizing first with
  | zero => simp [scanWords]
  | succ count ih =>
      simp only [scanWords, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨current, later⟩ i inside
        cases i with
        | zero => simpa only [Nat.add_zero] using current
        | succ i =>
            simpa only [Nat.add_assoc, Nat.add_comm 1 i] using later i (by omega)
      · intro every
        refine ⟨by simpa only [Nat.add_zero] using every 0 (by omega), ?_⟩
        intro i inside
        simpa only [Nat.add_assoc, Nat.add_comm 1 i] using every (i + 1) (by omega)

theorem scanWords_allWords (predicate : Nat → Bool) (count : Nat) :
    scanWords predicate 0 count = allWords predicate count := by
  apply Bool.eq_iff_iff.mpr
  simp only [scanWords_iff, allWords_iff, Nat.zero_add]

/-- No addition overflow occurs in the machine's ADD/ADC round-up. Its bound
comes from physically stored limb count, not from the logical natural's value. -/
theorem rounded_width_bound (index : NatOperand) (shift : Nat)
    (physical : index.words.length < 2 ^ 64) :
    bitLength index - shift + 63 < 2 ^ 128 := by
  have storage := bitLength_le_storage index
  omega

theorem rounded_word_count (bits : Nat) :
    (bits + 63) / 64 = bits / 64 + (if bits % 64 = 0 then 0 else 1) := by
  split <;> omega

theorem rounded_word_count_bound (index : NatOperand) (shift : Nat)
    (physical : index.words.length < 2 ^ 64) :
    (bitLength index - shift + 63) / 64 < 2 ^ 64 := by
  rw [rounded_word_count]
  exact prefix_word_count index shift physical

/-- This is the machine's unsigned high-half gate before the SHLD quotient.
Both halves are source u128 components, including shifts beyond all input bits. -/
theorem shift_offset_fits (low high : BitVec 64) :
    (low.toNat + 2 ^ 64 * high.toNat) / 64 < 2 ^ 64 ↔ high.toNat < 64 := by
  have lowBound := low.isLt
  omega

theorem shiftedWord_offset_overflow (index : NatOperand) (shift position : Nat)
    (overflow : 2 ^ 64 ≤ shift / 64 + position) :
    shiftedWord index shift position = 0 := by
  simp [shiftedWord, show ¬ shift / 64 + position < 2 ^ 64 by omega]

theorem shiftedWord_shift_overflow (index : NatOperand) (shift position : Nat)
    (overflow : 2 ^ 64 ≤ shift / 64) :
    shiftedWord index shift position = 0 := by
  simp [shiftedWord, show ¬ shift / 64 < 2 ^ 64 by omega]

/-- Exact source comparison, without replacing root/empty-prefix xor by a
numeric equality that is false outside the nonroot flip domain. -/
theorem prefixEqual_scan (left : NatOperand) (leftShift : Nat) (flip : Bool)
    (right : NatOperand) (rightShift : Nat)
    (physical : left.words.length < 2 ^ 64) :
    prefixEqual left leftShift flip right rightShift =
      if bitLength left - leftShift != bitLength right - rightShift then false else
        scanWords (fun i =>
          (shiftedWord left leftShift i ^^^ (if flip && i == 0 then 1 else 0)) ==
            shiftedWord right rightShift i) 0 ((bitLength left - leftShift + 63) / 64) := by
  rw [scanWords_allWords, rounded_word_count]
  have countBound := prefix_word_count left leftShift physical
  simp only [prefixEqual, Nat.mod_eq_of_lt countBound]

/-- The optional numerical interpretation is exported separately from the exact
source result: only this corollary uses the caller's nonroot flip argument. -/
theorem prefixEqual_numeric (left : NatOperand) (leftShift : Nat) (flip : Bool)
    (right : NatOperand) (rightShift : Nat)
    (leftPhysical : left.words.length < 2 ^ 64)
    (rightPhysical : right.words.length < 2 ^ 64)
    (domain : PrefixFlipDomain left leftShift flip) :
    prefixEqual left leftShift flip right rightShift =
      decide (((left.value >>> leftShift) ^^^ (if flip then 1 else 0)) =
        right.value >>> rightShift) :=
  prefixEqual_refines left leftShift flip right rightShift leftPhysical rightPhysical domain

end SszX86.IndicesPrefixEqual

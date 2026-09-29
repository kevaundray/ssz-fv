import SszIndicesArithmeticSemanticMasks
import SszNatAdd
import Ssz.Proofs.Merkle.Gindex

set_option autoImplicit false

namespace SszNative.Indices

theorem concatWord_eq (outer inner : NatOperand) (innerDepth position : Nat) :
    concatWord outer inner innerDepth position =
      NatShift.leftWord outer innerDepth position |||
        (word inner position &&& rangeWord position 0 innerDepth) := by
  have words : ∀ i, NatShift.word outer i = word outer i := fun i => (word_eq outer i).symm
  unfold concatWord NatShift.leftWord
  simp only [words]
  by_cases before : position < innerDepth / 64
  · simp [before, show ¬ innerDepth / 64 ≤ position by omega]
  · simp [before, show innerDepth / 64 ≤ position by omega]

theorem concatWord_bit (outer inner : NatOperand) (innerDepth position offset : Nat)
    (inside : offset < 64) :
    (concatWord outer inner innerDepth position).getLsbD offset =
      ((outer.value <<< innerDepth) ||| (inner.value % 2 ^ innerDepth)).testBit
        (64 * position + offset) := by
  rw [concatWord_eq, BitVec.getLsbD_or,
    NatShift.leftWord_bit outer innerDepth position offset inside,
    belowWord_bit inner innerDepth position offset inside]
  rw [Nat.testBit_or, Ssz.gindexBelow]

theorem inner_remainder (inner : Nat) (positive : 0 < inner) :
    inner % 2 ^ inner.log2 = inner - 2 ^ inner.log2 := by
  obtain ⟨lower, upper⟩ := Ssz.gindexDepth_bounds positive
  rw [Nat.pow_succ] at upper
  rw [Nat.mod_eq_sub_mod lower, Nat.mod_eq_of_lt (by omega)]

theorem concat_number (outer inner : Nat) (positive : 0 < inner) :
    ((outer <<< inner.log2) ||| (inner % 2 ^ inner.log2)) =
      outer * 2 ^ inner.log2 + (inner - 2 ^ inner.log2) := by
  rw [Nat.shiftLeft_eq, Nat.mul_comm outer,
    ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt inner (Nat.two_pow_pos inner.log2)) outer,
    inner_remainder inner positive, Nat.mul_comm]

theorem small_root_value (index : NatOperand)
    (root : index.wordCount ≤ 1 ∧ word index 0 = 1) : index.value = 1 := by
  have value := NatAdd.lowWord_value index root.1
  have low : NatAdd.lowWord index = word index 0 := (word_eq index 0).symm
  rw [low, root.2] at value
  exact value.symm

/-- The inner-root branch preserves the complete outer representation. -/
theorem concat_inner_root (outer inner : NatOperand) (base capacity used : Nat)
    (outerNonzero : outer.wordCount ≠ 0) (innerNonzero : inner.wordCount ≠ 0)
    (innerRoot : depth inner = 0) :
    concat outer inner base capacity used = unchanged used (.ok outer) := by
  simp [concat, checkedDepth, outerNonzero, innerNonzero, innerRoot]

/-- The outer-root shortcut is reached only after validating the inner index. -/
theorem concat_outer_root (outer inner : NatOperand) (base capacity used : Nat)
    (outerNonzero : outer.wordCount ≠ 0) (innerNonzero : inner.wordCount ≠ 0)
    (innerNotRoot : depth inner ≠ 0)
    (outerRoot : outer.wordCount ≤ 1 ∧ word outer 0 = 1) :
    concat outer inner base capacity used = unchanged used (.ok inner) := by
  simp [concat, checkedDepth, outerNonzero, innerNonzero, innerNotRoot, outerRoot]

theorem concat_value (outer inner : NatOperand) (base capacity used : Nat) (result : NatOperand)
    (_outerPhysical : outer.words.length < 2 ^ 64)
    (_innerPhysical : inner.words.length < 2 ^ 64)
    (success : (concat outer inner base capacity used).result = .ok result) :
    Ssz.gindexConcat outer.value inner.value = .ok result.value := by
  by_cases outerZero : outer.wordCount = 0
  · simp [concat, checkedDepth, outerZero, unchanged] at success
  by_cases innerZero : inner.wordCount = 0
  · simp [concat, checkedDepth, outerZero, innerZero, unchanged] at success
  have outerPositive : 0 < outer.value := by
    have nonzero : outer.value ≠ 0 := fun h => outerZero ((wordCount_zero_iff outer).mpr h)
    omega
  have innerPositive : 0 < inner.value := by
    have nonzero : inner.value ≠ 0 := fun h => innerZero ((wordCount_zero_iff inner).mpr h)
    omega
  have pinned : Ssz.gindexConcat outer.value inner.value =
      .ok (outer.value * 2 ^ depth inner + (inner.value - 2 ^ depth inner)) := by
    simp [Ssz.gindexConcat, Ssz.gindexDepth, depth_value,
      show ¬outer.value < 1 by omega, show ¬inner.value < 1 by omega]
    rfl
  rw [pinned]
  apply congrArg Except.ok
  symm
  simp only [concat, checkedDepth, outerZero, innerZero, ↓reduceIte] at success
  split at success
  · rename_i root
    simp only [unchanged, Except.ok.injEq] at success
    subst result
    have depthZero : inner.value.log2 = 0 := by simpa only [depth_value] using root
    have bound := Nat.lt_log2_self (n := inner.value)
    rw [depthZero] at bound
    have innerOne : inner.value = 1 := by omega
    simp [root, innerOne]
  · split at success
    · rename_i root
      simp only [unchanged, Except.ok.injEq] at success
      subst result
      have outerOne := small_root_value outer root
      have lower := Nat.log2_self_le (by omega : inner.value ≠ 0)
      rw [← depth_value inner] at lower
      simp only [outerOne, Nat.one_mul]
      omega
    · split at success
      · cases counted : wordCount (bitLength outer + depth inner) with
        | error reason => simp [counted, unchanged] at success
        | ok count =>
            simp only [counted] at success
            split at success
            · have value : result.value =
                  ((outer.value <<< depth inner) ||| (inner.value % 2 ^ depth inner)) := by
                apply makeNat_value_of_bits count base capacity used _ _ result
                  (concatWord_bit outer inner (depth inner)) _ success
                intro position past
                have cover := wordCount_covers (bitLength outer + depth inner) count counted
                rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow]
                have above : depth inner ≤ position := by omega
                have notBelow : ¬position < depth inner := by omega
                simp only [above, decide_true, Bool.true_and, notBelow, decide_false,
                  Bool.false_and, Bool.or_false]
                apply NatShift.bit_false
                rw [NatShift.bitLength, ← bitLength_value]
                omega
              rw [value, depth_value, concat_number outer.value inner.value innerPositive]
            · cases success
      · cases success

end SszNative.Indices

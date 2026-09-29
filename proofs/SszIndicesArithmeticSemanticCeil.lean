import SszIndicesArithmeticSemanticCeilCarry
import SszHashLayoutArithmetic

set_option autoImplicit false

namespace SszNative.Indices

theorem lowMask_word_value (index : NatOperand) (shift : Nat) (bounded : shift ≤ 64) :
    (word index 0 &&& lowMask shift).toNat = index.value % 2 ^ shift := by
  apply Nat.eq_of_testBit_eq
  intro position
  rw [BitVec.testBit_toNat, BitVec.getLsbD_and, lowMask_bit shift position bounded,
    Nat.testBit_mod_two_pow]
  by_cases inside : position < 64
  · rw [word_bit index 0 position inside]
    simp [Bool.and_comm]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega)]
    have outside : ¬position < shift := by omega
    simp [outside]

theorem lowMask_word_zero_iff (index : NatOperand) (shift : Nat) (bounded : shift ≤ 64) :
    word index 0 &&& lowMask shift = 0 ↔ index.value % 2 ^ shift = 0 := by
  rw [BitVec.toNat_eq, lowMask_word_value index shift bounded]
  rfl

theorem ceilShift_value (index : NatOperand) (shift base capacity used : Nat) (result : NatOperand)
    (physical : index.words.length < 2 ^ 64) (bounded : shift ≤ 64)
    (success : (ceilShift index shift base capacity used).result = .ok result) :
    result.value = (index.value + 2 ^ shift - 1) / 2 ^ shift := by
  have identity := HashLayout.ceiling_identity index.value (2 ^ shift) (Nat.two_pow_pos shift)
  unfold ceilShift at success
  split at success
  · rename_i exactShift
    have zero : index.value % 2 ^ shift = 0 :=
      (lowMask_word_zero_iff index shift bounded).mp (by simpa only [beq_iff_eq] using exactShift)
    have shifted : (NatShift.shr index shift base capacity used).result = .ok result := by
      cases actual : (NatShift.shr index shift base capacity used).result with
      | error reason => simp [arithmetic, actual, Except.mapError] at success
      | ok operand =>
          simp only [arithmetic, actual, Except.mapError, Except.ok.injEq] at success
          subst operand
          rfl
    have value := NatShift.shr_value index shift base capacity used result shifted
    rw [value, Nat.shiftRight_eq_div_pow]
    simpa only [zero, ↓reduceIte] using identity
  · rename_i rounded
    have nonzero : index.value % 2 ^ shift ≠ 0 := by
      intro zero
      have masked := (lowMask_word_zero_iff index shift bounded).mpr zero
      simp [masked] at rounded
    have target : (index.value >>> shift) + 1 =
        (index.value + 2 ^ shift - 1) / 2 ^ shift := by
      simpa only [nonzero, ↓reduceIte, Nat.shiftRight_eq_div_pow] using identity
    cases counted : wordCount (bitLength index - shift) with
    | error reason => simp [counted, unchanged] at success
    | ok count =>
        have covers := wordCount_covers (bitLength index - shift) count counted
        cases count with
        | zero =>
            simp only [counted, unchanged, Except.ok.injEq] at success
            subst result
            have quotient : index.value >>> shift = 0 := by
              apply Nat.eq_of_testBit_eq
              intro position
              rw [shifted_bit_false index shift position (by omega), Nat.zero_testBit]
            change 1 = (index.value + 2 ^ shift - 1) / 2 ^ shift
            simpa only [quotient, Nat.zero_add] using target
        | succ count =>
            simp only [counted] at success
            split at success
            · split at success
              · have enough : bitLength index - shift ≤ 64 * (count + 2) := by omega
                have oldBound := shifted_value_lt index shift (count + 1) physical covers
                have positive := Nat.two_pow_pos (64 * (count + 1))
                have power : 2 ^ (64 * (count + 2)) =
                    2 ^ (64 * (count + 1)) * 2 ^ 64 := by
                  rw [← Nat.pow_add]
                  congr 1
                have fits : (index.value >>> shift) + 1 < 2 ^ (64 * (count + 2)) := by
                  rw [power]
                  omega
                rw [makeNatState_success_value (count + 2) base capacity used true
                  (ceilStep index shift) result success,
                  ceilFill_value index shift (count + 2) physical enough fits, target]
              · cases success
            · rename_i notFull
              have oldBound := shifted_value_lt index shift (count + 1) physical covers
              have notMaximum : index.value >>> shift ≠ 2 ^ (64 * (count + 1)) - 1 := by
                intro maximum
                exact notFull (shifted_all_max index shift (count + 1) physical maximum)
              have fits : (index.value >>> shift) + 1 < 2 ^ (64 * (count + 1)) := by
                apply Nat.lt_of_le_of_ne (Nat.succ_le_of_lt oldBound)
                intro equal
                apply notMaximum
                rw [← equal]
                omega
              rw [makeNatState_success_value (count + 1) base capacity used true
                (ceilStep index shift) result success,
                ceilFill_value index shift (count + 1) physical covers fits, target]

end SszNative.Indices

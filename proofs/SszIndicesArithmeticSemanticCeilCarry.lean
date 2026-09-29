import SszIndicesArithmeticSemanticShift

set_option autoImplicit false

namespace SszNative.Indices

theorem shiftedWords_value (index : NatOperand) (shift count : Nat)
    (physical : index.words.length < 2 ^ 64)
    (enough : bitLength index - shift ≤ 64 * count) :
    Limbs.value (List.ofFn (fun i : Fin count => shiftedWord index shift i.val)) =
      index.value >>> shift := by
  have generators : (fun i : Fin count => shiftedWord index shift i.val) =
      (fun i : Fin count => NatShift.shiftedWord index shift i.val) := by
    funext i
    exact shiftedWord_eq_native index shift i.val physical
  rw [generators]
  apply NatShift.rightWords_value
  simpa only [NatShift.bitLength, ← bitLength_value] using enough

theorem shifted_value_lt (index : NatOperand) (shift count : Nat)
    (physical : index.words.length < 2 ^ 64)
    (enough : bitLength index - shift ≤ 64 * count) :
    index.value >>> shift < 2 ^ (64 * count) := by
  have bounded := Limbs.value_lt
    (List.ofFn (fun i : Fin count => shiftedWord index shift i.val))
  simpa only [List.length_ofFn, shiftedWords_value index shift count physical enough] using bounded

theorem ceilStep_balance (index : NatOperand) (shift position : Nat) (carry : Bool) :
    (ceilStep index shift position carry).1.toNat +
      2 ^ 64 * (if (ceilStep index shift position carry).2 then 1 else 0) =
        (shiftedWord index shift position).toNat + (if carry then 1 else 0) := by
  have bounded := (shiftedWord index shift position).isLt
  cases carry with
  | false =>
      simp [ceilStep, show ¬2 ^ 64 ≤ (shiftedWord index shift position).toNat by omega]
  | true =>
      simp only [ceilStep, ↓reduceIte, BitVec.toNat_add,
        (show (1 : BitVec 64).toNat = 1 from rfl), decide_eq_true_eq]
      split <;> omega

/-- The literal mutable initializer conserves the input limbs plus the incoming
carry, with the outgoing carry above the complete initialized prefix. -/
theorem ceilFill_balance (index : NatOperand) (shift position count : Nat) (carry : Bool) :
    Limbs.value (fillWords (ceilStep index shift) position count carry).1 +
      2 ^ (64 * count) * (if (fillWords (ceilStep index shift) position count carry).2 then 1 else 0) =
        Limbs.value (List.ofFn (fun i : Fin count => shiftedWord index shift (position + i.val))) +
          (if carry then 1 else 0) := by
  induction count generalizing position carry with
  | zero => cases carry <;> rfl
  | succ count ih =>
      have recursive := ih (position + 1) (ceilStep index shift position carry).2
      have multiplied := congrArg (fun value : Nat => 2 ^ 64 * value) recursive
      have step := ceilStep_balance index shift position carry
      have offset : (fun i : Fin count => shiftedWord index shift (position + (i.val + 1))) =
          (fun i : Fin count => shiftedWord index shift (position + 1 + i.val)) := by
        funext i
        congr 1
        omega
      have power : 2 ^ (64 * (count + 1)) = 2 ^ 64 * 2 ^ (64 * count) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      simp only [fillWords, List.ofFn_succ, Limbs.value, Fin.val_zero, Nat.add_zero,
        Fin.val_succ, offset, power, Nat.mul_assoc]
      simp only [Nat.mul_add] at multiplied
      rcases Bool.eq_false_or_eq_true
        (fillWords (ceilStep index shift) (position + 1) count
          (ceilStep index shift position carry).2).2 with last | last <;>
        simp only [last, Bool.false_eq_true, ↓reduceIte,
          Nat.mul_zero, Nat.mul_one, Nat.add_zero] at multiplied ⊢ <;> omega

theorem shifted_all_max (index : NatOperand) (shift count : Nat)
    (physical : index.words.length < 2 ^ 64)
    (maximum : index.value >>> shift = 2 ^ (64 * count) - 1) :
    allWords (fun i => shiftedWord index shift i == -1) count = true := by
  apply (allWords_iff _ count).mpr
  intro position inside
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro offset small
  have mask : (-1 : BitVec 64).getLsbD offset = decide (offset < 64) := by
    change (2 ^ 64 - 1).testBit offset = decide (offset < 64)
    exact Nat.testBit_two_pow_sub_one 64 offset
  rw [shiftedWord_bit index shift position offset physical small, maximum,
    Nat.testBit_two_pow_sub_one, mask]
  simp only [small, decide_true]
  exact decide_eq_true (by omega)

theorem ceilFill_value (index : NatOperand) (shift count : Nat)
    (physical : index.words.length < 2 ^ 64)
    (enough : bitLength index - shift ≤ 64 * count)
    (fits : (index.value >>> shift) + 1 < 2 ^ (64 * count)) :
    Limbs.value (fillWords (ceilStep index shift) 0 count true).1 =
      (index.value >>> shift) + 1 := by
  have balance := ceilFill_balance index shift 0 count true
  simp only [Nat.zero_add, ↓reduceIte,
    shiftedWords_value index shift count physical enough] at balance
  cases carried : (fillWords (ceilStep index shift) 0 count true).2 <;>
    simp only [carried, Bool.false_eq_true, ↓reduceIte,
      Nat.mul_zero, Nat.mul_one, Nat.add_zero] at balance
  · exact balance
  · omega

end SszNative.Indices

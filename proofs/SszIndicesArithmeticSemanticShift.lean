import SszIndicesArithmeticSemanticMake

set_option autoImplicit false

namespace SszNative.Indices

theorem one_bit (position : Nat) : (1 : Nat).testBit position = decide (position = 0) := by
  simpa [eq_comm] using (Nat.testBit_two_pow (n := 0) (m := position))

theorem xorWord_bit (index : NatOperand) (shift : Nat) (flip : Bool)
    (position offset : Nat) (physical : index.words.length < 2 ^ 64) (inside : offset < 64) :
    (shiftedWord index shift position ^^^ (if flip && position == 0 then 1 else 0)).getLsbD offset =
      ((index.value >>> shift) ^^^ (if flip then 1 else 0)).testBit (64 * position + offset) := by
  rw [BitVec.getLsbD_xor, shiftedWord_bit index shift position offset physical inside,
    Nat.testBit_xor]
  congr 1
  cases flip with
  | false => simp
  | true =>
      by_cases zero : position = 0
      · simp [zero, one_bit]
      · simp [zero, one_bit] <;> omega

theorem shifted_bit_false (index : NatOperand) (shift position : Nat)
    (past : bitLength index - shift ≤ position) :
    (index.value >>> shift).testBit position = false := by
  rw [Nat.testBit_shiftRight]
  apply NatShift.bit_false
  rw [NatShift.bitLength, ← bitLength_value]
  omega

theorem shiftXor_value (index : NatOperand) (shift : Nat) (flip : Bool)
    (base capacity used : Nat) (result : NatOperand)
    (physical : index.words.length < 2 ^ 64)
    (success : (shiftXor index shift flip base capacity used).result = .ok result) :
    result.value = (index.value >>> shift) ^^^ (if flip then 1 else 0) := by
  unfold shiftXor at success
  cases counted : wordCount (bitLength index - shift) with
  | error reason => simp [counted, unchanged] at success
  | ok count =>
      simp only [counted] at success
      apply makeNat_value_of_bits _ base capacity used _ _ result
        (fun position offset inside => xorWord_bit index shift flip position offset physical inside)
        _ success
      intro position past
      have cover := wordCount_covers (bitLength index - shift) count counted
      have count_le : count ≤ max count (if flip then 1 else 0) := Nat.le_max_left _ _
      rw [Nat.testBit_xor, shifted_bit_false index shift position (by omega)]
      cases flip with
      | false => simp
      | true =>
          change 64 * max count 1 ≤ position at past
          have nonzero : position ≠ 0 := by
            have lower : 1 ≤ max count 1 := Nat.le_max_right _ _
            omega
          simp [one_bit, nonzero]

theorem sibling_value (index : NatOperand) (base capacity used : Nat) (result : NatOperand)
    (physical : index.words.length < 2 ^ 64)
    (success : (sibling index base capacity used).result = .ok result) :
    result.value = Ssz.gindexSibling index.value := by
  simpa [Ssz.gindexSibling] using
    shiftXor_value index 0 true base capacity used result physical success

theorem parent_value (index : NatOperand) (base capacity used : Nat) (result : NatOperand)
    (success : (parent index base capacity used).result = .ok result) :
    result.value = Ssz.gindexParent index.value := by
  have shifted : (NatShift.shr index 1 base capacity used).result = .ok result := by
    cases value : (NatShift.shr index 1 base capacity used).result with
    | error reason => simp [parent, arithmetic, value, Except.mapError] at success
    | ok operand =>
        simp only [parent, arithmetic, value, Except.mapError, Except.ok.injEq] at success
        subst operand
        rfl
  simpa [Ssz.gindexParent, Nat.shiftRight_eq_div_pow] using
    NatShift.shr_value index 1 base capacity used result shifted

end SszNative.Indices

import SszIndicesArithmeticSemanticConcat
import SszIndicesArithmeticSemanticShift

set_option autoImplicit false

namespace SszNative.Indices

theorem child_eq_or (index : Nat) (right : Bool) :
    Ssz.gindexChild index right = (index <<< 1) ||| (if right then 1 else 0) := by
  have bound : (if right then 1 else 0 : Nat) < 2 ^ 1 := by cases right <;> decide
  simpa [Ssz.gindexChild, Nat.shiftLeft_eq, Nat.mul_comm] using
    Nat.two_pow_add_eq_or_of_lt bound index

theorem childWord_eq (index : NatOperand) (right : Bool) (position : Nat) :
    ((word index position <<< 1) |||
      (if position = 0 then (if right then 1#64 else 0#64) else word index (position - 1) >>> 63)) =
      NatShift.leftWord index 1 position ||| (if position = 0 then (if right then 1#64 else 0#64) else 0#64) := by
  have words : ∀ i, NatShift.word index i = word index i := fun i => (word_eq index i).symm
  by_cases zero : position = 0
  · simp [NatShift.leftWord, words, zero]
  · simp [NatShift.leftWord, words, zero]

theorem childWord_bit (index : NatOperand) (right : Bool) (position offset : Nat)
    (inside : offset < 64) :
    ((word index position <<< 1) |||
      (if position = 0 then (if right then 1#64 else 0#64) else word index (position - 1) >>> 63)).getLsbD offset =
        (Ssz.gindexChild index.value right).testBit (64 * position + offset) := by
  rw [childWord_eq, BitVec.getLsbD_or, NatShift.leftWord_bit index 1 position offset inside,
    child_eq_or, Nat.testBit_or]
  congr 1
  cases right with
  | false => simp
  | true =>
      by_cases zero : position = 0
      · simp [zero, one_bit]
      · simp [zero, one_bit] <;> omega

theorem child_value (index : NatOperand) (right : Bool) (base capacity used : Nat)
    (result : NatOperand) (success : (child index right base capacity used).result = .ok result) :
    result.value = Ssz.gindexChild index.value right := by
  unfold child at success
  split at success
  · rename_i zero
    have valueZero := (wordCount_zero_iff index).mp zero
    simp only [unchanged, Except.ok.injEq] at success
    subst result
    rw [Ssz.gindexChild, valueZero]
    cases right <;> rfl
  · split at success
    · cases counted : wordCount (bitLength index + 1) with
      | error reason => simp [counted, unchanged] at success
      | ok count =>
          simp only [counted] at success
          apply makeNat_value_of_bits count base capacity used _ _ result
            (childWord_bit index right) _ success
          intro position past
          have covers := wordCount_covers (bitLength index + 1) count counted
          have positive : 1 ≤ position := by omega
          have nonzero : position ≠ 0 := by omega
          rw [child_eq_or, Nat.testBit_or, Nat.testBit_shiftLeft]
          simp only [positive, decide_true, Bool.true_and]
          have empty : index.value.testBit (position - 1) = false := by
            apply NatShift.bit_false
            rw [NatShift.bitLength, ← bitLength_value]
            omega
          rw [empty]
          cases right <;> simp [one_bit, nonzero]
    · cases success

end SszNative.Indices

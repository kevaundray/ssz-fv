import SszX86.NatMulOwnership

namespace SszX86.NatMul
open SszNative
open UintCodec

/-- This is derived from the original byte span, not a logical magnitude cap. -/
theorem operand_words_bound (m : DataMem) (operand : NatOperand)
    (stored : operand.At (widthLoad m)) : operand.words.length < 2^61 := by
  cases operand with
  | small limb => decide
  | large pointer words =>
    have positive := stored.1
    have extent := stored.2.2.1
    change words.length < 2^61
    omega

theorem operand_count_bound (m : DataMem) (operand : NatOperand)
    (stored : operand.At (widthLoad m)) : operand.wordCount < 2^61 :=
  Nat.lt_of_le_of_lt (Limbs.sigWords_le_length operand.words) (operand_words_bound m operand stored)

/-- The checked count-add overflow edge is ruled out by physical input spans;
reserve's byte-size, alignment, and capacity errors remain genuine branches. -/
theorem Owned.count_add_fits {s : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra) :
    left.wordCount + right.wordCount < 2^64 := by
  have leftBound := operand_count_bound s.dmem left owned.left_at
  have rightBound := operand_count_bound s.dmem right owned.right_at
  omega

end SszX86.NatMul

import SszX86.NatMulWordMath
import SszX86.NatAddCarryPairMath

namespace SszX86.NatMulWord
open SszNative

/-- The two-word unroll is exactly two iterations of the checked helper loop. -/
theorem inner_two (remaining index : Nat) (factor : BitVec 64)
    (words : List (BitVec 64)) (carry : Nat) :
    LimbMul.inner (remaining+2) factor (words.drop index) [] carry =
      let first := LimbMul.step factor (words[index]?.getD 0) 0 carry
      let second := LimbMul.step factor (words[index+1]?.getD 0) 0 first.2
      let rest := LimbMul.inner remaining factor (words.drop (index+2)) [] second.2
      (first.1 :: second.1 :: rest.1, rest.2) := by
  have first := LimbMul.inner_indexed_succ (remaining+1) index factor words [] carry
  have second := LimbMul.inner_indexed_succ remaining (index+1) factor words []
    (LimbMul.step factor (words[index]?.getD 0) 0 carry).2
  simp only [List.drop_nil, List.getElem?_nil, Option.getD_none] at first second
  rw [show remaining+2 = (remaining+1)+1 by omega, first, second]

/-- The last source index is zero even if a physical redundant suffix remains.
Thus the odd tail's two-operand IMUL loses no information needed by mul_word. -/
theorem final_input_zero (operand : NatOperand) :
    operand.words[operand.wordCount]?.getD 0 = 0 := by
  rw [← SszNative.NatAdd.trim_word]
  rw [NatOperand.wordCount_eq_trim_length]
  simp

theorem final_step (factor : BitVec 64) (carry : Nat) (bound : carry < 2^64) :
    LimbMul.step factor 0 0 carry = (BitVec.ofNat 64 carry, 0) := by
  simp only [LimbMul.step, show (0 : BitVec 64).toNat = 0 by decide,
    Nat.mul_zero, Nat.zero_add, Nat.div_eq_of_lt bound]

/-- Count parity determines whether the unrolled body writes the extra carry
word itself or leaves exactly one word for the original IMUL tail. -/
theorem unrolled_geometry (count : Nat) (large : 1 < count) :
    1 ≤ count / 2 ∧
      1 + 2 * (count / 2) + (count % 2) = count + 1 ∧ count % 2 ≤ 1 := by omega

/-- The mask in R12 removes the low parity bit after the checked byte-length
bound has already excluded the high three bits. -/
theorem paired_count (count : BitVec 64) (bound : count.toNat < 2^61) :
    count &&& 2305843009213693950#64 = BitVec.ofNat 64 (count.toNat / 2 * 2) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.and_comm, Nat.mul_comm]
    using NatAdd.Carry.even_mask count.toNat bound

end SszX86.NatMulWord

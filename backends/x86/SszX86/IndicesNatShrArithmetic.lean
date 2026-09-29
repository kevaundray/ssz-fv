import SszIndicesArithmeticSemanticShift
import SszNatShiftResources

set_option autoImplicit false

namespace SszX86.IndicesNatShr
open SszNative

/-- On the compiler-specialized internal domain there is no whole-limb offset.
Zero is kept separate: the machine's complementary shift is masked to zero at
that amount, whereas the source omits the carry limb entirely. -/
theorem shiftedWord_internal (operand : NatOperand) (bits position : Nat)
    (amount : bits ≤ 8) :
    NatShift.shiftedWord operand bits position =
      if bits = 0 then NatShift.word operand position
      else (NatShift.word operand position >>> bits) |||
        (NatShift.word operand (position + 1) <<< (64 - bits)) := by
  have small : bits < 64 := by omega
  simp only [NatShift.shiftedWord, Nat.div_eq_of_lt small, Nat.mod_eq_of_lt small,
    Nat.add_zero]
  by_cases zero : bits = 0
  · simp [zero]
  · simp [zero]

/-- The logical complement is already in the hardware's six-bit count range on
all nonzero specialized calls. It must not be used for the normalization arm. -/
theorem complementary_count (bits : Nat) (positive : 0 < bits) (amount : bits ≤ 8) :
    56 ≤ 64 - bits ∧ 64 - bits < 64 ∧ (64 - bits) % 64 = 64 - bits := by
  have small : 64 - bits < 64 := by omega
  exact ⟨by omega, small, Nat.mod_eq_of_lt small⟩

/-- The indices initializer can reuse the same carry equation without requiring
canonical input limbs or bounding the value represented by them. -/
theorem indices_shiftedWord_internal (operand : NatOperand) (bits position : Nat)
    (physical : operand.words.length < 2 ^ 64) (amount : bits ≤ 8) :
    Indices.shiftedWord operand bits position =
      if bits = 0 then Indices.word operand position
      else (Indices.word operand position >>> bits) |||
        (Indices.word operand (position + 1) <<< (64 - bits)) := by
  rw [Indices.shiftedWord_eq_native operand bits position physical,
    shiftedWord_internal operand bits position amount]
  simp only [Indices.word_eq, NatShift.word]

/-- The allocation arm cannot be entered by Small or a one-word Large input.
Thus the original Small-buffer zero-fill branch is unreachable from a source
Nat::shr call, rather than an extra caller restriction on representations. -/
theorem allocation_input (operand : NatOperand) (bits : Nat)
    (large : 64 < NatShift.bitLength operand - bits) :
    ∃ pointer words, operand = .large pointer words ∧ 1 < words.length := by
  have width := NatShift.bitLength_physical operand
  cases operand with
  | small limb =>
      simp only [NatOperand.words, List.length_cons, List.length_nil] at width
      omega
  | large pointer words =>
      refine ⟨pointer, words, rfl, ?_⟩
      change NatShift.bitLength (.large pointer words) ≤ 64 * words.length at width
      omega

/-- Every output loop iteration is bounded by the original physical limb count,
including noncanonical high zeros. The successor is a zero-extended observation
when it equals that count. -/
theorem output_count_bound (operand : NatOperand) (bits : Nat)
    (live : bits < NatShift.bitLength operand) :
    NatShift.wordCount (NatShift.bitLength operand - bits) ≤ operand.words.length := by
  have width := NatShift.bitLength_physical operand
  unfold NatShift.wordCount
  omega

end SszX86.IndicesNatShr

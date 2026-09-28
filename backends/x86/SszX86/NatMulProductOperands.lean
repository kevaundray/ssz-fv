import SszX86.NatMulProductBounds

namespace SszX86.NatMul.Product
open SszNative

/-- Both operands reaching the row-major branch are genuinely pointer-backed.
Thus the small and out-of-range word-fetch arms are unreachable for real row indices. -/
theorem large_of_count (operand : NatOperand) (large : 1 < operand.wordCount) :
    ∃ pointer words, operand = .large pointer words := by
  cases operand with
  | small limb =>
    have bound := significant_le_physical (.small limb)
    simp only [NatOperand.words, List.length_cons, List.length_nil] at bound
    omega
  | large pointer words => exact ⟨pointer, words, rfl⟩

/-- Redundant high zero limbs do not change any indexed observation before the
significant bound, and the physical payload may be strictly greater. -/
theorem original_index_bound (operand : NatOperand) (index : Nat)
    (inside : index < operand.wordCount) : index < operand.words.length := by
  have bound := significant_le_physical operand
  omega

end SszX86.NatMul.Product

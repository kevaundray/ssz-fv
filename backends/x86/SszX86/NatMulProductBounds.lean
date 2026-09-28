import SszX86.NatMulCore

namespace SszX86.NatMul.Product
open SszNative

/-- The actual byte span, rather than a logical limb cap, bounds the counters. -/
theorem physical_counts (dst : BitVec 64) (left right : Nat)
    (span : dst.toNat + 8 * (left + right) ≤ 2^64) :
    left + right < 2^64 := by omega

/-- The inner indexed write at PC583 is strictly inside the allocated sum. -/
theorem inner_index_lt (left right row column : Nat)
    (rowBound : row < left) (columnBound : column < right) :
    row + column < left + right := by omega

/-- The explicit carry overwrite at PC633 is also inside that same allocation. -/
theorem carry_index_lt (left right row : Nat) (rowBound : row < left) :
    row + right < left + right := by omega

/-- Neither address calculation wraps before either native bounds comparison. -/
theorem inner_guard (left right row column : Nat)
    (physical : left + right < 2^64)
    (rowBound : row < left) (columnBound : column < right) :
    (BitVec.ofNat 64 row + BitVec.ofNat 64 column).toNat <
      (BitVec.ofNat 64 (left + right)).toNat := by
  have bound := inner_index_lt left right row column rowBound columnBound
  bv_omega

theorem carry_guard (left right row : Nat)
    (physical : left + right < 2^64) (rowBound : row < left) :
    (BitVec.ofNat 64 row + BitVec.ofNat 64 right).toNat <
      (BitVec.ofNat 64 (left + right)).toNat := by
  have bound := carry_index_lt left right row rowBound
  bv_omega

/-- Significant counts of a genuinely allocating operand fit its original span. -/
theorem significant_le_physical (operand : NatOperand) :
    operand.wordCount ≤ operand.words.length := by
  exact Limbs.sigWords_le_length operand.words

end SszX86.NatMul.Product

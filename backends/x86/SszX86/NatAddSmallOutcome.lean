import SszX86.NatAddSmallMath

namespace SszX86.NatAdd
open SszNative

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem overflow_high (left right : NatOperand)
    (overflow : ¬ (SszNative.NatAdd.sumWide left right).toNat < 2^64) :
    ((SszNative.NatAdd.sumWide left right) >>> 64).setWidth 64 = 1#64 := by
  have carry : 2^64 ≤ (SszNative.NatAdd.lowWord left).toNat + (SszNative.NatAdd.lowWord right).toNat := by
    simp only [SszNative.NatAdd.sumWide, LimbAdd.wideSum_toNat _ _ 0 (by omega), Nat.add_zero] at overflow
    omega
  simp [SszNative.NatAdd.sumWide, wide_high, carry]

/-- The native overflow branch writes exactly two words, including its literal
one in the carry slot. This uses the ordered zero/count gates of the shared run. -/
theorem one_word_overflow (left right : NatOperand) (address capacity used : Nat)
    (leftNonzero : left.wordCount ≠ 0) (rightNonzero : right.wordCount ≠ 0)
    (small : left.wordCount ≤ 1 ∧ right.wordCount ≤ 1)
    (overflow : ¬ (SszNative.NatAdd.sumWide left right).toNat < 2^64) :
    SszNative.NatAdd.run left right address capacity used =
      match Arena.reserve address capacity used 2 with
      | none => NatArithmetic.unchanged used (.error .scratchExhausted)
      | some reservation => NatArithmetic.committed reservation
          [(SszNative.NatAdd.sumWide left right).setWidth 64, 1#64] := by
  rw [SszNative.NatAdd.run_one_word left right address capacity used leftNonzero rightNonzero small]
  cases reserved : Arena.reserve address capacity used 2 <;>
    simp only [NatArithmetic.fromWide, overflow, ↓reduceIte, reserved, overflow_high left right overflow]

end SszX86.NatAdd

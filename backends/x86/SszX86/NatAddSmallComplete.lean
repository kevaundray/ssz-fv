import SszX86.NatAddSmallReturn
import SszX86.NatAddSmallOverflowReturn

namespace SszX86.NatAdd
open SszNative

/-- Both native one-word arithmetic outcomes execute through the real RET,
including reserve failure and overflow's exact two-word commitment. -/
theorem sum_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra)
    (ready : SumReady (pushedState s) t left right)
    (leftNonzero : left.wordCount ≠ 0) (rightNonzero : right.wordCount ≠ 0)
    (small : left.wordCount ≤ 1 ∧ right.wordCount ≤ 1) :
    Eventually (step e) (Post s left right address capacity used ra)
      (t, sumTarget left right base) := by
  unfold sumTarget
  by_cases fits : (SszNative.NatAdd.sumWide left right).toNat < 2^64
  · rw [ite_eq_left fits]
    exact small_fit_finish_cps e base hc s t left right address capacity used ra owned ready
      leftNonzero rightNonzero small fits
  · rw [ite_eq_right fits]
    exact small_overflow_finish_cps e base hc s t left right address capacity used ra owned ready
      leftNonzero rightNonzero small fits

end SszX86.NatAdd

import SszArm.NatMulZero
import SszArm.NatMulTail
import SszArm.NatMulLarge

namespace SszArm.NatMul

/-- Complete original main entry through its original RET. Raw operand scans
select zero, right-one, left-one, or the checked row-major allocating loop. -/
theorem program_correct (s : ArmState) (base : BitVec 64)
    (left right : SszNative.NatOperand)
    (code : JointCodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (owned : Owned s left right)
    (pc : read_pc s = base + BitVec.ofNat 64 entry) :
    ∃ fuel t, run fuel s = t ∧ Post s t left right := by
  by_cases zero : left.wordCount = 0 ∨ right.wordCount = 0
  · exact zero_run s base left right owned code error aligned pc zero
  have leftNonzero : left.wordCount ≠ 0 := fun h => zero (Or.inl h)
  have rightNonzero : right.wordCount ≠ 0 := fun h => zero (Or.inr h)
  by_cases one : right.wordCount = 1 ∨ left.wordCount = 1
  · exact word_branch_run s base left right owned code error aligned pc leftNonzero rightNonzero one
  · apply large_run s base left right owned code error aligned pc
    · omega
    · omega

end SszArm.NatMul

import SszArm.NatDivisionClassifiedFast
import SszArm.NatDivisionFastPaths

namespace SszArm.NatDivision

/-- Full native entry-through-RET for physically Large operands selected by the
fast branch. The physical limb list remains unrestricted, including padding. -/
theorem large_fast_correct (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (owned : Owned s (.large pointer words))
    (code : JointCodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base)
    (count : (SszNative.NatOperand.large pointer words).wordCount ≤ 2) :
    ∃ fuel, Post s (run fuel s) (.large pointer words) := by
  obtain ⟨entryFuel, current, entryRun, classified⟩ :=
    classify_run s base (.large pointer words) owned code.1 error aligned pc
  have cc : JointCodeAt current base := by
    simpa only [JointCodeAt, CodeAt, Udivti3.CodeAt, SszArm.CodeAt, classified.program] using code
  obtain ⟨site, start, input⟩ := classified_large_fast s current base pointer words owned classified count
  obtain ⟨fuel, post⟩ := fast_correct s current base site (.large pointer words) owned
    classified.saved classified.out classified.divisor classified.arena cc classified.error
    classified.aligned start count input classified.frame
  refine ⟨entryFuel + fuel, ?_⟩
  rw [run_plus, entryRun]
  exact post

end SszArm.NatDivision

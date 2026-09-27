import SszArm.NatDivisionLargeReserved

namespace SszArm.NatDivision

open SszNative.Limbs

/-- Full native entry-through-RET for the allocated unbounded Large path.
The successful reservation is a pure model case, not an execution hypothesis. -/
theorem large_success_correct (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (reservation : SszNative.Arena.Reservation)
    (owned : Owned s (.large pointer words)) (code : JointCodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) (pc : read_pc s = base)
    (count : 2 < sigWords words)
    (reserve : SszNative.Arena.reserve (arenaOf s).base (arenaOf s).capacity
      (arenaOf s).used (sigWords words) = some reservation) :
    ∃ fuel, Post s (run fuel s) (.large pointer words) := by
  obtain ⟨entryFuel, current, entryRun, classified⟩ :=
    classify_run s base (.large pointer words) owned code.1 error aligned pc
  have cc : JointCodeAt current base := by
    simpa only [JointCodeAt, CodeAt, Udivti3.CodeAt, SszArm.CodeAt, classified.program] using code
  have branch := classified.large_state owned count
  obtain ⟨fuel, post⟩ := large_guard_reserved_post s current base pointer words reservation owned
    classified.saved classified.out classified.arena cc classified.error classified.aligned
    branch.1 classified.pointer classified.payload branch.2.1 classified.divisor
    branch.2.2.1 branch.2.2.2.1 count reserve classified.frame
  refine ⟨entryFuel + fuel, ?_⟩
  rw [run_plus, entryRun]
  exact post

end SszArm.NatDivision

import SszArm.NatDivisionLargeEntry
import SszArm.NatDivisionLargeExhausted

namespace SszArm.NatDivision

open SszNative.Limbs

/-- Full native entry-through-RET when a Large operand has more than two
significant input limbs and the unsigned checked reservation is exhausted. -/
theorem large_failure_correct (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (owned : Owned s (.large pointer words))
    (code : JointCodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base)
    (count : 2 < sigWords words)
    (reserve : SszNative.Arena.reserve (arenaOf s).base (arenaOf s).capacity
      (arenaOf s).used (sigWords words) = none) :
    ∃ fuel, Post s (run fuel s) (.large pointer words) := by
  obtain ⟨entryFuel, current, entryRun, classified⟩ :=
    classify_run s base (.large pointer words) owned code.1 error aligned pc
  have cc : CodeAt current base := by
    simpa only [CodeAt, SszArm.CodeAt, classified.program] using code.1
  have branch := classified.large_state owned count
  have countNat : (r (.GPR 8#5) current).toNat = sigWords words := by
    rw [branch.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt owned.large_count_bound]
  have positive : 0 < (r (.GPR 8#5) current).toNat := by rw [countNat]; omega
  have reserveNative : SszNative.Arena.reserve (arenaOf s).base (arenaOf s).capacity
      (arenaOf s).used (r (.GPR 8#5) current).toNat = none := by rw [countNat]; exact reserve
  have source := SszNative.NatDivision.phase_reserve_failure (.large pointer words)
    (r (.GPR 3#5) s) (arenaOf s).base (arenaOf s).capacity (arenaOf s).used
    owned.divisor_nonzero owned.divisor_ne_one count reserve
  have failed : (outcome s (.large pointer words)).result = .error .scratchExhausted := by
    rw [source]
    rfl
  obtain ⟨fuel, post⟩ := large_exhausted_post s current base (.large pointer words) owned
    classified.saved classified.out classified.arena cc classified.error classified.aligned
    branch.1 positive failed reserveNative classified.frame
  refine ⟨entryFuel + fuel, ?_⟩
  rw [run_plus, entryRun]
  exact post

end SszArm.NatDivision

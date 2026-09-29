import SszArm.NatMulLargeFailure
import SszArm.NatMulLargeSuccess

namespace SszArm.NatMul

/-- Original entry through original RET for the allocating branch. Reservation
failure is classified by the executed size/resource guards; success obtains its
initialized memory only from the shipped memset and row-major multiplication. -/
theorem large_run (s : ArmState) (base : BitVec 64)
    (left right : SszNative.NatOperand) (owned : Owned s left right)
    (code : JointCodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 entry)
    (largeLeft : 1 < left.wordCount) (largeRight : 1 < right.wordCount) :
    ∃ fuel t, run fuel s = t ∧ Post s t left right := by
  obtain ⟨entryFuel, u, entryRun, entryFrame, dispatch, leftAt, rightAt⟩ :=
    entry_dispatch s base left right owned code.body error aligned pc
  have start := large_start entryFrame dispatch largeLeft largeRight
  obtain ⟨reserveFuel, v, reserveRun, classified⟩ := reserve_runs u base
    (read_mem_bytes 8 (r (.GPR 5#5) s) s)
    (read_mem_bytes 8 (r (.GPR 5#5) s + 8#64) s)
    (read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) s)
    (entryFrame.jointCode code) (entryFrame.error.trans error) (entryFrame.aligned aligned)
    start.pc (by rw [start.count owned]; omega)
    (ReturnSpace.of_owned owned entryFrame.saved).stack
    (by simpa only [BitVec.add_zero] using start.header owned 0 (by decide))
    (start.header owned 8 (by decide)) (start.header owned 16 (by decide))
    (by rw [entryFrame.arena]; exact owned.arenaBound) (start.header_stack owned)
    owned.arenaStorage (start.cursor_separate owned largeLeft largeRight)
  rw [start.count owned] at classified
  rcases classified with failure | success
  · rcases failure with ⟨kind, ⟨middle, sizeFrame, checksFrame⟩, memory⟩
    have branch : ∃ path : ReturnErrorPath,
        read_pc v = base + BitVec.ofNat 64 path.start ∧
        outcome s left right = SszNative.NatArithmetic.unchanged (arenaOf s).used (.error .scratchExhausted) := by
      rcases kind with ⟨overflow, failedPC⟩ | ⟨exhausted, failedPC⟩
      · refine ⟨.sizeOverflow, failedPC, ?_⟩
        exact reserve_model_failure left right (arenaOf s).base (arenaOf s).capacity (arenaOf s).used
          largeLeft largeRight (Or.inl overflow)
      · refine ⟨.scratch, failedPC, ?_⟩
        exact reserve_model_failure left right (arenaOf s).base (arenaOf s).capacity (arenaOf s).used
          largeLeft largeRight (Or.inr exhausted)
    obtain ⟨path, failedPC, model⟩ := branch
    obtain ⟨returnFuel, t, returnRun, post⟩ := large_failure_return path s u v base left right owned
      entryFrame middle sizeFrame checksFrame memory code.body error aligned failedPC model
    refine ⟨entryFuel + (reserveFuel + returnFuel), t, ?_, post⟩
    rw [run_plus, entryRun, run_plus, reserveRun, returnRun]
  · rcases success with ⟨reservation, reserved, ready, memory⟩
    have allocated := large_reservation owned largeLeft largeRight reservation reserved
    obtain ⟨returnFuel, t, returnRun, post⟩ := large_success_return s u v base left right owned start
      largeLeft largeRight reservation allocated ready memory code aligned
    refine ⟨entryFuel + (reserveFuel + returnFuel), t, ?_, post⟩
    rw [run_plus, entryRun, run_plus, reserveRun, returnRun]

end SszArm.NatMul

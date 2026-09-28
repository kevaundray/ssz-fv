import SszArm.BitVectorRound
import SszArm.BitVectorArithmeticFailureDivision

namespace SszArm.BitVector

/-- Complete linked body execution from physical postdispatch entry. The only
case splits are shared arithmetic outcomes and the actual division remainder;
all corresponding native branches and helper calls are proved, not assumed. -/
theorem body_correct (s : ArmState) (base : BitVec 64)
    (length : SszNative.NatOperand) (data : Ssz.Bytes)
    (owned : Owned s length data) (code : JointCodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 428#64) :
    ∃ fuel t, run fuel s = t ∧ Completed s t base length data := by
  obtain ⟨divisionFuel, d, divisionRun, post, current, statusCurrent, statusCode, statusBefore⟩ :=
    entry_checks_division s base length data owned code error aligned pc
  let checked := Block.divisionStatusResult d base
  have statusFrame := division_status_frame owned current base
  cases division : (SszNative.NatDivision.run length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used).result with
  | error reason =>
    have failure : (outcome s length data).divided.result = .error reason := by
      simpa only [outcome, divided_eq] using division
    have model := division_error_model s length data reason division
    have resources := (division_resources owned post model.2).after_local owned statusFrame
    obtain ⟨failureFuel, final, failureRun, terminal, failureFrame⟩ :=
      ArithmeticFailure.division_failure owned current post failure statusCode aligned
    have whole : run (divisionFuel + failureFuel) s = final := by
      rw [run_plus, divisionRun, failureRun]
    refine ⟨divisionFuel + failureFuel, final, whole, ?_⟩
    refine ⟨?_, resources.after_local owned failureFrame,
      statusBefore.trans ((local_covered s (outcome s length data)).frame failureFrame), ?_⟩
    · rw [model.1]
      exact terminal
    · rw [← failureRun]
      exact statusCode.run _
  | ok value =>
    obtain ⟨quotient, remainder⟩ := value
    have success : (outcome s length data).divided.result = .ok (quotient, remainder) := by
      simpa only [outcome, divided_eq] using division
    obtain ⟨counted, statusPC, savedPair⟩ := division_status_success owned current post success
    let copied := ExpectedStage.Stage.division.result checked base
    have copiedRun : run 3 checked = copied := ExpectedStage.executes .division checked base
      statusCode.body counted.error (counted.toWorking.aligned aligned) statusPC
    have copiedCurrent := counted.after_expected .division base
    have copiedFrame := expected_frame owned counted.toWorking .division base
    have copiedCode : JointCodeAt copied base := by
      rw [← copiedRun]
      exact statusCode.run 3
    have copiedBefore := statusBefore.trans ((local_covered s (outcome s length data)).frame copiedFrame)
    have limbs := quotient_local_owned owned division
    have pair := division_expected_pair (base := base) owned counted.toWorking savedPair limbs
    have copiedPC := division_expected_pc (base := base) counted
    by_cases zero : remainder = 0#64
    · have model := division_zero_model s length quotient remainder data division zero
      have resources := ((division_resources owned post model.2).after_local owned statusFrame).after_local
        owned copiedFrame
      have frontier : ExpectedAt s copied base length quotient remainder data := by
        refine ⟨copiedCurrent, ?_, copiedCode, pair, limbs, ?_, model.1, resources, copiedBefore⟩
        · simpa only [if_pos zero] using copiedPC
        · exact SszNative.BitVector.expected_of_division length quotient remainder
            (arenaOf s).base (arenaOf s).capacity (arenaOf s).used division zero
      obtain ⟨finishFuel, final, finishRun, completed⟩ := expected_executes owned aligned frontier
      have whole : run (divisionFuel + 3 + finishFuel) s = final := by
        rw [run_plus, run_plus, divisionRun, copiedRun, finishRun]
      exact ⟨divisionFuel + 3 + finishFuel, final, whole, completed⟩
    · have arena := ((division_arena owned post).after_local owned statusFrame).after_local owned copiedFrame
      have buffers := divided_after_local owned copiedFrame
        (divided_after_local owned statusFrame (division_buffers owned post))
      have arenaRegister : r (.GPR 19#5) copied = r (.GPR 19#5) s := by
        simpa (config := {decide := true}) [copied, ExpectedStage.Stage.result, state_simp_rules]
          using division_arena_register post
      have roundPC : read_pc copied = base + 3392#64 := by
        simpa only [if_neg zero] using copiedPC
      obtain ⟨finishFuel, final, finishRun, completed⟩ := rounding_completes owned copiedCurrent pair arena
        buffers arenaRegister division zero copiedBefore copiedCode aligned roundPC
      have whole : run (divisionFuel + 3 + finishFuel) s = final := by
        rw [run_plus, run_plus, divisionRun, copiedRun, finishRun]
      exact ⟨divisionFuel + 3 + finishFuel, final, whole, completed⟩

end SszArm.BitVector

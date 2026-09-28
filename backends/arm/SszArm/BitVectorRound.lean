import SszArm.BitVectorRoundSuccess
import SszArm.BitVectorExpected
import SszArm.BitVectorArithmeticFailureRound

namespace SszArm.BitVector

open UintCodec (widthLoad)
open Delimited (MemoryFrame)

/-- The nonzero-remainder branch performs the actual optional allocation. Both
its failure and every continuation after its success retain both full buffers. -/
theorem rounding_completes {s c : ArmState} {base : BitVec 64}
    {length quotient : SszNative.NatOperand} {data : Ssz.Bytes} {remainder : BitVec 64}
    (owned : Owned s length data) (current : Counted s c length remainder)
    (pair : SszNative.NatArithmetic.operandAt (widthLoad c)
      (r (.GPR 31#5) s + 48#64).toNat quotient)
    (arena : ArenaAt s c (outcome s length data).divided.used)
    (buffers : SszNative.BitVector.allocationAt (widthLoad c) (outcome s length data).divided)
    (arenaRegister : r (.GPR 19#5) c = r (.GPR 19#5) s)
    (division : (SszNative.NatDivision.run length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used).result = .ok (quotient, remainder))
    (nonzero : remainder ≠ 0#64)
    (before : MemoryFrame (writesFor s (outcome s length data)) s c)
    (code : JointCodeAt c base) (aligned : CheckSPAlignment s)
    (pc : read_pc c = base + 3392#64) :
    ∃ fuel t, run fuel c = t ∧ Completed s t base length data := by
  have args := round_arguments base owned current.toWorking pair arena arenaRegister
  obtain ⟨roundFuel, rounded, roundRun, roundPost, roundCurrent, roundCode, roundPC, roundFrame⟩ :=
    rounding_executes base owned current pair arena arenaRegister division nonzero code aligned pc
  have preparation : MemoryFrame (localWrites s) c (roundEntry c base) := by
    apply frame_of_memory
    simp only [roundEntry, called, Stages.CallPreparation.result, state_simp_rules]
  have resources := rounded_resources owned args division nonzero
    (arena.after_local owned preparation) (divided_after_local owned preparation buffers) roundPost
  have afterRound := before.trans roundFrame
  cases addition : (rounding s length quotient).result with
  | error reason =>
    obtain ⟨failureFuel, final, failureRun, terminal, failureFrame⟩ :=
      ArithmeticFailure.rounding_failure owned roundCurrent.toWorking roundPost args addition
        roundCode aligned roundPC
    have whole : run (roundFuel + failureFuel) c = final := by
      rw [run_plus, roundRun, failureRun]
    refine ⟨roundFuel + failureFuel, final, whole, ?_⟩
    refine ⟨?_, resources.after_local owned failureFrame,
      afterRound.trans ((local_covered s (outcome s length data)).frame failureFrame), ?_⟩
    · rw [round_error_model s length quotient remainder data reason division nonzero addition]
      exact terminal
    · rw [← failureRun]
      exact roundCode.run _
  | ok expected =>
    obtain ⟨pairFuel, paired, pairRun, frontier⟩ := round_success_expected owned roundCurrent roundPost
      args division nonzero addition resources afterRound roundCode aligned roundPC
    obtain ⟨finishFuel, final, finishRun, completed⟩ := expected_executes owned aligned frontier
    have whole : run (roundFuel + pairFuel + finishFuel) c = final := by
      rw [run_plus, run_plus, roundRun, pairRun, finishRun]
    exact ⟨roundFuel + pairFuel + finishFuel, final, whole, completed⟩

end SszArm.BitVector

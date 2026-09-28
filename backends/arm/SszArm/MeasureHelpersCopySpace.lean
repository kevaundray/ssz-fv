import SszArm.MeasureBitsPropagationCopy
import SszArm.MeasureMemory

namespace SszArm.Measure.Helpers

open SszNative.Serialize (Desc Value)

theorem original_copy_space {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (u : ArmState)
    (output : r (.GPR 19#5) u = args.result) (stack : r (.GPR 31#5) u = args.bodySP)
    (failure : (outcome s args desc value).result = .error (.arithmetic .scratchExhausted))
    (twoCalls : (outcome s args desc value).calls.length = 2) :
    Bits.Propagation.CopySpace u := by
  have low := owned.stackLow
  have extent : resultExtent (outcome s args desc value) = 72 := by
    simp [resultExtent, propagated, failure, twoCalls]
  have bound : args.result.toNat + 72 ≤ 2^64 := by simpa only [extent] using owned.resultBound
  have fields := owned.resultStack (args.result.toNat, 72)
    (by simp [resultWrites, failure, extent])
  have scratch : args.result.toNat + 72 ≤ args.stack.toNat - 152 ∨
      args.stack.toNat - 152 + 68 ≤ args.result.toNat := by
    rcases fields with empty | separate
    · omega
    · exact separate (args.stack.toNat - 152, 68)
        (by simp [stackWrites, bodyStackWrites, twoCalls])
  have saved : args.result.toNat + 72 ≤ args.stack.toNat - 80 ∨
      args.stack.toNat - 80 + 80 ≤ args.result.toNat := by
    rcases fields with empty | separate
    · omega
    · exact separate (args.stack.toNat - 80, 80) (by simp [stackWrites, saveWrites])
  refine ⟨?_, ?_, ?_⟩
  · simpa only [output] using bound
  · rw [stack, Args.bodySP]
    bv_omega
  · rw [output, stack, Args.bodySP]
    bv_omega

end SszArm.Measure.Helpers

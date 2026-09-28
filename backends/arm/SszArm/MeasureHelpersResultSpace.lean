import SszArm.MeasureResultFields
import SszArm.MeasureMemory

namespace SszArm.Measure.Helpers

open SszNative.Serialize (Desc Value Error)
open Delimited (Protected)

private theorem extent_lower (measured : SszNative.Serialize.Outcome SszNative.NatOperand) :
    68 ≤ resultExtent measured := by
  unfold resultExtent
  split <;> decide

theorem original_success_space {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (u : ArmState)
    (output : r (.GPR 19#5) u = args.result) (stack : r (.GPR 31#5) u = args.bodySP) :
    Result.SuccessSpace u := by
  have low := owned.stackLow
  have bound := owned.resultBound
  have extent := extent_lower (outcome s args desc value)
  have pre : Protected (stackWrites args (outcome s args desc value)) args.result.toNat 40 := by
    cases measured : (outcome s args desc value).result with
    | ok operand => exact owned.resultStack (args.result.toNat, 40) (by simp [resultWrites, measured])
    | error reason =>
      have full := owned.resultStack (args.result.toNat, resultExtent (outcome s args desc value))
        (by simp [resultWrites, measured])
      simpa only [Nat.add_zero] using full.subspan 0 40 (by omega)
  have flag : Protected (stackWrites args (outcome s args desc value)) (args.result.toNat + 64) 4 := by
    cases measured : (outcome s args desc value).result with
    | ok operand => exact owned.resultStack (args.result.toNat + 64, 4) (by simp [resultWrites, measured])
    | error reason =>
      have full := owned.resultStack (args.result.toNat, resultExtent (outcome s args desc value))
        (by simp [resultWrites, measured])
      exact full.subspan 64 4 (by omega)
  have prefixSeparate : args.result.toNat + 40 ≤ args.stack.toNat - 288 ∨
      args.stack.toNat - 288 + 16 ≤ args.result.toNat := by
    rcases pre with empty | separate
    · omega
    · exact separate (args.stack.toNat - 288, 16) (by simp [stackWrites, bodyStackWrites])
  have flagSeparate : args.result.toNat + 68 ≤ args.stack.toNat - 288 ∨
      args.stack.toNat - 288 + 16 ≤ args.result.toNat + 64 := by
    rcases flag with empty | separate
    · omega
    · simpa only [Nat.add_assoc] using separate (args.stack.toNat - 288, 16)
        (by simp [stackWrites, bodyStackWrites])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stack, Args.bodySP]; bv_omega
  · rw [output]; omega
  · rw [output, stack, Args.bodySP]; bv_omega
  · rw [output, stack, Args.bodySP]; bv_omega

theorem original_error_space {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (u : ArmState)
    (output : r (.GPR 19#5) u = args.result) (stack : r (.GPR 31#5) u = args.bodySP)
    (reason : Error) (failure : (outcome s args desc value).result = .error reason) :
    Result.ErrorSpace u := by
  have low := owned.stackLow
  have bound := owned.resultBound
  have extent := extent_lower (outcome s args desc value)
  have full := owned.resultStack (args.result.toNat, resultExtent (outcome s args desc value))
    (by simp [resultWrites, failure])
  have separate : args.result.toNat + 68 ≤ args.stack.toNat - 288 ∨
      args.stack.toNat - 288 + 16 ≤ args.result.toNat := by
    rcases full with empty | apartFrom
    · omega
    · have apart := apartFrom (args.stack.toNat - 288, 16) (by simp [stackWrites, bodyStackWrites])
      dsimp at apart
      omega
  refine ⟨?_, ?_, ?_⟩
  · rw [stack, Args.bodySP]; bv_omega
  · rw [output]; omega
  · rw [output, stack, Args.bodySP]; bv_omega

end SszArm.Measure.Helpers

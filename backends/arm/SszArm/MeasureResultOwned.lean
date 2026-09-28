import SszArm.MeasureResultFields
import SszArm.MeasurePost

namespace SszArm.Measure.Result

open SszNative.Serialize (Desc Value)

theorem success_space {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (output : r (.GPR 19#5) s = args.result)
    (stack : r (.GPR 31#5) s = args.bodySP) (operand : SszNative.NatOperand)
    (success : (outcome s args desc value).result = .ok operand) : SuccessSpace s := by
  have low := owned.stackLow
  have bound := owned.resultBound
  have fields := owned.resultStack (args.result.toNat, 40) (by simp [resultWrites, success])
  have status := owned.resultStack (args.result.toNat + 64, 4) (by simp [resultWrites, success])
  have fieldsSep : args.result.toNat + 40 ≤ args.stack.toNat - 288 ∨
      args.stack.toNat - 288 + 16 ≤ args.result.toNat := by
    rcases fields with empty | separate
    · omega
    · exact separate (args.stack.toNat - 288, 16) (by simp [stackWrites, bodyStackWrites])
  have statusSep : args.result.toNat + 68 ≤ args.stack.toNat - 288 ∨
      args.stack.toNat - 288 + 16 ≤ args.result.toNat + 64 := by
    rcases status with empty | separate
    · omega
    · simpa using separate (args.stack.toNat - 288, 16) (by simp [stackWrites, bodyStackWrites])
  simp only [resultExtent, propagated, success] at bound
  constructor
  · rw [stack, Args.bodySP]; bv_omega
  · simpa [output] using bound
  · rw [output, stack, Args.bodySP]; bv_omega
  · rw [output, stack, Args.bodySP]; bv_omega

theorem error_space {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (output : r (.GPR 19#5) s = args.result)
    (stack : r (.GPR 31#5) s = args.bodySP)
    (wrong : (outcome s args desc value).result = .error .wrongType) : ErrorSpace s := by
  have low := owned.stackLow
  have bound := owned.resultBound
  have extent : resultExtent (outcome s args desc value) = 68 := by
    simp [resultExtent, propagated, wrong]
  rw [extent] at bound
  have fields := owned.resultStack (args.result.toNat, 68)
    (by simp [resultWrites, wrong, extent])
  have separated : args.result.toNat + 68 ≤ args.stack.toNat - 288 ∨
      args.stack.toNat - 288 + 16 ≤ args.result.toNat := by
    rcases fields with empty | separate
    · omega
    · exact separate (args.stack.toNat - 288, 16) (by simp [stackWrites, bodyStackWrites])
  constructor
  · rw [stack, Args.bodySP]; bv_omega
  · simpa [output] using bound
  · rw [output, stack, Args.bodySP]; bv_omega

theorem success_writes {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (low : 288 ≤ args.stack.toNat) (output : r (.GPR 19#5) s = args.result)
    (stack : r (.GPR 31#5) s = args.bodySP) (operand : SszNative.NatOperand)
    (success : (outcome s args desc value).result = .ok operand)
    (noCalls : (outcome s args desc value).calls = []) :
    successWrites s = bodyWrites args (outcome s args desc value) := by
  have position : (r (.GPR 31#5) s).toNat - 16 = args.stack.toNat - 288 := by
    rw [stack, Args.bodySP]; bv_omega
  simp [successWrites, bodyWrites, bodyStackWrites, resultWrites, allocationWrites,
    success, noCalls, output, position]

theorem wrong_writes {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (low : 288 ≤ args.stack.toNat) (output : r (.GPR 19#5) s = args.result)
    (stack : r (.GPR 31#5) s = args.bodySP)
    (wrong : (outcome s args desc value).result = .error .wrongType)
    (noCalls : (outcome s args desc value).calls = []) :
    errorWrites s = bodyWrites args (outcome s args desc value) := by
  have position : (r (.GPR 31#5) s).toNat - 16 = args.stack.toNat - 288 := by
    rw [stack, Args.bodySP]; bv_omega
  simp [errorWrites, bodyWrites, bodyStackWrites, resultWrites, allocationWrites,
    resultExtent, propagated, wrong, noCalls, output, position]

end SszArm.Measure.Result

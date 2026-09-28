import SszArm.MeasureErrorWritersFields
import SszArm.MeasurePost

namespace SszArm.Measure.Result

open SszNative.Serialize (Desc Value Error)

theorem semantic_error_space {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (output : r (.GPR 19#5) s = args.result)
    (stack : r (.GPR 31#5) s = args.bodySP) (reason : Error)
    (failure : (outcome s args desc value).result = .error reason)
    (inlineError : propagated (outcome s args desc value) = false) : ErrorSpace s := by
  have low := owned.stackLow
  have bound := owned.resultBound
  have extent : resultExtent (outcome s args desc value) = 68 := by
    simp [resultExtent, inlineError]
  rw [extent] at bound
  have fields := owned.resultStack (args.result.toNat, 68)
    (by simp [resultWrites, failure, extent])
  have separated : args.result.toNat + 68 ≤ args.stack.toNat - 288 ∨
      args.stack.toNat - 288 + 16 ≤ args.result.toNat := by
    rcases fields with empty | separate
    · omega
    · exact separate (args.stack.toNat - 288, 16) (by simp [stackWrites, bodyStackWrites])
  constructor
  · rw [stack, Args.bodySP]
    bv_omega
  · simpa only [output] using bound
  · rw [output, stack, Args.bodySP]
    bv_omega

theorem semantic_error_writes {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (low : 288 ≤ args.stack.toNat) (output : r (.GPR 19#5) s = args.result)
    (stack : r (.GPR 31#5) s = args.bodySP) (reason : Error)
    (failure : (outcome s args desc value).result = .error reason)
    (inlineError : propagated (outcome s args desc value) = false)
    (noCalls : (outcome s args desc value).calls = []) :
    errorWrites s = bodyWrites args (outcome s args desc value) := by
  have position : (r (.GPR 31#5) s).toNat - 16 = args.stack.toNat - 288 := by
    rw [stack, Args.bodySP]
    bv_omega
  simp [errorWrites, bodyWrites, bodyStackWrites, resultWrites, allocationWrites,
    resultExtent, failure, inlineError, noCalls, output, position]

theorem scope_produced {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (base : BitVec 64) (owned : Owned s args desc value)
    (output : r (.GPR 19#5) s = args.result) (stack : r (.GPR 31#5) s = args.bodySP)
    (expected : SszNative.NatOperand) (actual : BitVec 64)
    (failure : (outcome s args desc value).result = .error (.scope expected (.small actual)))
    (noCalls : (outcome s args desc value).calls = [])
    (used : (outcome s args desc value).used = (arenaOf s args).used)
    (pointer : r (.GPR 8#5) s = expected.pointer)
    (payload : r (.GPR 9#5) s = expected.payload)
    (actualWord : r (.GPR 20#5) s = actual)
    (input : expected.At (UintCodec.widthLoad s))
    (borrowed : NatDivision.OperandOwned (bodyWrites args (outcome s args desc value)) expected)
    (error : read_err s = .None) : Produced s (scopeResult s base) args desc value base := by
  have inlineError : propagated (outcome s args desc value) = false := by simp [propagated, failure]
  have space := semantic_error_space owned output stack _ failure inlineError
  have writes := semantic_error_writes owned.stackLow output stack _ failure inlineError noCalls
  apply Produced.of_no_calls owned noCalls used (scope_pc s base) (scope_program s base)
    ((scope_error s base).trans error) ((scope_sp s base).trans stack)
  · rw [failure, ← output]
    simpa only [actualWord] using scope_at s base space expected pointer payload input
      (by simpa only [writes] using borrowed)
  · simpa only [writes] using scope_frame s base space
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      exact scope_register s base _ (by decide) (by decide) (by decide) (by decide)
  · intro reg low high
    rw [scope_vector]

theorem limit_produced {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (base : BitVec 64) (owned : Owned s args desc value)
    (output : r (.GPR 19#5) s = args.result) (stack : r (.GPR 31#5) s = args.bodySP)
    (expected : SszNative.NatOperand) (actual : BitVec 64)
    (failure : (outcome s args desc value).result = .error (.limit expected (.small actual)))
    (noCalls : (outcome s args desc value).calls = [])
    (used : (outcome s args desc value).used = (arenaOf s args).used)
    (pointer : r (.GPR 8#5) s = expected.pointer)
    (payload : r (.GPR 9#5) s = expected.payload)
    (actualWord : r (.GPR 20#5) s = actual)
    (input : expected.At (UintCodec.widthLoad s))
    (borrowed : NatDivision.OperandOwned (bodyWrites args (outcome s args desc value)) expected)
    (error : read_err s = .None) : Produced s (limitResult s base) args desc value base := by
  have inlineError : propagated (outcome s args desc value) = false := by simp [propagated, failure]
  have space := semantic_error_space owned output stack _ failure inlineError
  have writes := semantic_error_writes owned.stackLow output stack _ failure inlineError noCalls
  apply Produced.of_no_calls owned noCalls used (limit_pc s base) (limit_program s base)
    ((limit_error s base).trans error) ((limit_sp s base).trans stack)
  · rw [failure, ← output]
    simpa only [actualWord] using limit_at s base space expected pointer payload input
      (by simpa only [writes] using borrowed)
  · simpa only [writes] using limit_frame s base space
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      exact limit_register s base _ (by decide) (by decide) (by decide) (by decide)
  · intro reg low high
    rw [limit_vector]

end SszArm.Measure.Result

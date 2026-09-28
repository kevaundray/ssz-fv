import SszArm.MeasureBitsScratchFields
import SszArm.MeasureUnallocatedPost
import SszArm.MeasureErrorWritersProduced

namespace SszArm.Measure.Bits.Scratch

open SszNative.Serialize (Desc Value)
open Result

theorem inline_space {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (output : r (.GPR 19#5) s = args.result)
    (stack : r (.GPR 31#5) s = args.bodySP)
    (failure : (outcome s args desc value).result = .error (.arithmetic .scratchExhausted))
    (notPropagated : (outcome s args desc value).calls.length ≠ 2) : ErrorSpace s := by
  exact semantic_error_space owned output stack _ failure
    (by simp [propagated, failure, notPropagated])

theorem inline_produced {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (base : BitVec 64) (owned : Owned s args desc value)
    (output : r (.GPR 19#5) s = args.result) (stack : r (.GPR 31#5) s = args.bodySP)
    (failure : (outcome s args desc value).result = .error (.arithmetic .scratchExhausted))
    (notPropagated : (outcome s args desc value).calls.length ≠ 2)
    (unallocated : ∀ call ∈ (outcome s args desc value).calls, call.allocation = none)
    (unchanged : (outcome s args desc value).used = (arenaOf s args).used)
    (error : read_err s = .None) : Produced s (finalResult s base) args desc value base := by
  have space := inline_space owned output stack failure notPropagated
  have lower : (r (.GPR 31#5) s).toNat - 16 = args.stack.toNat - 288 := by
    have low := owned.stackLow
    rw [stack, Args.bodySP]
    bv_omega
  have extent : resultExtent (outcome s args desc value) = 68 := by
    simp [resultExtent, propagated, failure, notPropagated]
  have noWrites := allocationWrites_of_unallocated args (outcome s args desc value) unallocated
  have writes : errorWrites s = bodyWrites args (outcome s args desc value) := by
    simp only [errorWrites, bodyWrites, bodyStackWrites, resultWrites, failure,
      notPropagated, ↓reduceIte, List.append_nil, noWrites, extent, lower, output]
    rfl
  apply Produced.of_unallocated owned unallocated unchanged (final_pc s base) (final_program s base)
    ((final_error s base).trans error) ((final_sp s base).trans stack)
  · rw [failure, ← output]
    exact final_at s base space
  · simpa only [writes] using final_frame s base space
  · intro reg member
    have untouched : reg ≠ 8#5 ∧ reg ≠ 9#5 ∧ reg ≠ 10#5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    exact final_register s base reg untouched.1 untouched.2.1 untouched.2.2
  · intro reg low high
    exact congrArg (fun word : BitVec 128 => word.setWidth 64) (final_vector s base reg)

end SszArm.Measure.Bits.Scratch

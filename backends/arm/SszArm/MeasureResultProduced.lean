import SszArm.MeasureResultOwned

namespace SszArm.Measure.Result

open SszNative.Serialize (Desc Value)

theorem success_produced {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (base : BitVec 64) (owned : Owned s args desc value)
    (output : r (.GPR 19#5) s = args.result) (stack : r (.GPR 31#5) s = args.bodySP)
    (operand : SszNative.NatOperand)
    (success : (outcome s args desc value).result = .ok operand)
    (noCalls : (outcome s args desc value).calls = [])
    (used : (outcome s args desc value).used = (arenaOf s args).used)
    (pointer : r (.GPR 21#5) s = operand.pointer)
    (payload : r (.GPR 20#5) s = operand.payload)
    (input : operand.At (UintCodec.widthLoad s))
    (borrowed : NatDivision.OperandOwned (bodyWrites args (outcome s args desc value)) operand)
    (error : read_err s = .None) :
    Produced s (successResult s base) args desc value base := by
  have space := success_space owned output stack operand success
  have writes := success_writes owned.stackLow output stack operand success noCalls
  apply Produced.of_no_calls owned noCalls used (success_pc s base) (success_program s base)
    ((success_error s base).trans error) ((success_sp s base).trans stack)
  · rw [success, ← output]
    exact success_at s base space operand pointer payload input (by simpa only [writes] using borrowed)
  · simpa only [writes] using success_frame s base space
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      exact success_register s base _ (by decide) (by decide) (by decide)
  · intro reg low high
    rw [success_vector]

theorem wrong_produced {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (base : BitVec 64) (owned : Owned s args desc value)
    (output : r (.GPR 19#5) s = args.result) (stack : r (.GPR 31#5) s = args.bodySP)
    (wrong : (outcome s args desc value).result = .error .wrongType)
    (noCalls : (outcome s args desc value).calls = [])
    (used : (outcome s args desc value).used = (arenaOf s args).used)
    (error : read_err s = .None) :
    Produced s (wrongResult s base) args desc value base := by
  have space := error_space owned output stack wrong
  have writes := wrong_writes owned.stackLow output stack wrong noCalls
  apply Produced.of_no_calls owned noCalls used (wrong_pc s base) (wrong_program s base)
    ((wrong_error s base).trans error) ((wrong_sp s base).trans stack)
  · rw [wrong, ← output]
    exact wrong_at s base space
  · simpa only [writes] using wrong_frame s base space
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      exact wrong_register s base _ (by decide) (by decide) (by decide)
  · intro reg low high
    rw [wrong_vector]

end SszArm.Measure.Result

import SszArm.MeasureScalarBool
import SszArm.MeasureScalarTransition

namespace SszArm.Measure.Scalar

open SszNative.Serialize (Value)

private theorem bool_success_body (s : ArmState) (base : BitVec 64) (args : Args) (flag : Bool)
    (owned : Owned s args .bool (.bool flag)) (registers : BodyRegisters s args)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 760#64) (tag : (r (.GPR 8#5) s).setWidth 32 = 0#32) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args .bool (.bool flag) base := by
  let u := boolReady s base
  have pre : run 4 s = u := bool_ready_run s base code error pc tag
  have up : u.program = s.program := by simp [u, boolReady, state_simp_rules]
  have ue : read_err u = .None := by simpa [u, boolReady, state_simp_rules] using error
  have ua : CheckSPAlignment u := by
    simpa (config := {decide := true}) [u, boolReady, CheckSPAlignment, state_simp_rules] using aligned
  have uo : r (.GPR 19#5) u = args.result := by
    simpa (config := {decide := true}) [u, boolReady, state_simp_rules] using registers.result
  have us : r (.GPR 31#5) u = args.bodySP := by
    simpa (config := {decide := true}) [u, boolReady, state_simp_rules] using registers.stack
  have own : Owned u args .bool (.bool flag) := owned.of_local_frame (by
    intro address outside
    simp [u, boolReady, ArmState.mem_w_eq_mem])
  have post := Result.success_produced base own uo us (.small 1#64)
    (by rfl) (by rfl) (by rfl)
    (by simp [u, boolReady, SszNative.NatOperand.pointer, state_simp_rules])
    (by simp [u, boolReady, SszNative.NatOperand.payload, state_simp_rules])
    (by trivial) (by trivial) ue
  refine ⟨37, Result.successResult u base, ?_, prepend_pure post up ?_ ?_ ?_⟩
  · rw [show 37 = 4 + 33 by decide, run_plus, pre]
    exact Result.success_run u base (code.congr up) ue ua
      (by simp [u, boolReady, state_simp_rules])
  · simp [u, boolReady, ArmState.mem_w_eq_mem]
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [u, boolReady, state_simp_rules]
  · intro reg low high
    simp [u, boolReady, state_simp_rules]

private theorem bool_wrong_body (s : ArmState) (base : BitVec 64) (args : Args) (value : Value)
    (owned : Owned s args .bool value) (registers : BodyRegisters s args)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 760#64) (tag : (r (.GPR 8#5) s).setWidth 32 ≠ 0#32)
    (wrong : (outcome s args .bool value).result = .error .wrongType) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args .bool value base := by
  let u := w .PC (base + 3924#64) s
  have pre : run 1 s = u := bool_wrong_run s base code error pc tag
  have up : u.program = s.program := by simp [u, state_simp_rules]
  have ue : read_err u = .None := by simpa [u, state_simp_rules] using error
  have ua : CheckSPAlignment u := by simpa [u, CheckSPAlignment, state_simp_rules] using aligned
  have uo : r (.GPR 19#5) u = args.result := by simpa [u, state_simp_rules] using registers.result
  have us : r (.GPR 31#5) u = args.bodySP := by simpa [u, state_simp_rules] using registers.stack
  have own : Owned u args .bool value := owned.of_local_frame (by
    intro address outside
    simp [u, ArmState.mem_w_eq_mem])
  have same : outcome u args .bool value = outcome s args .bool value := by
    simp [outcome, arenaOf, u, state_simp_rules]
  have calls : (outcome u args .bool value).calls = [] := by cases value <;> rfl
  have used : (outcome u args .bool value).used = (arenaOf u args).used := by cases value <;> rfl
  have post := Result.wrong_produced base own uo us (by simpa only [same] using wrong) calls used ue
  refine ⟨49, Result.wrongResult u base, ?_, prepend_pure post up ?_ ?_ ?_⟩
  · rw [show 49 = 1 + 48 by decide, run_plus, pre]
    exact Result.wrong_run u base (code.congr up) ue ua (by simp [u, state_simp_rules])
  · simp [u, ArmState.mem_w_eq_mem]
  · intro reg member; simp [u, state_simp_rules]
  · intro reg low high; simp [u, state_simp_rules]

end SszArm.Measure.Scalar

namespace SszArm.Measure

open SszNative.Serialize (Value)

theorem bool_body (s : ArmState) (base : BitVec 64) (args : Args) (value : Value)
    (owned : Owned s args .bool value) (registers : BodyRegisters s args)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 760#64) (_descriptor : r (.GPR 1#5) s = args.descriptor)
    (tag : r (.GPR 8#5) s = (Emit.valueTag value).setWidth 64) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args .bool value base := by
  cases value with
  | bool flag =>
    exact Scalar.bool_success_body s base args flag owned registers code error aligned pc
      (by simp [tag, Emit.valueTag])
  | uint number | bytes number | bits number | seq number =>
    exact Scalar.bool_wrong_body s base args _ owned registers code error aligned pc
      (by simp [tag, Emit.valueTag]) (by rfl)
  | union selector content =>
    exact Scalar.bool_wrong_body s base args _ owned registers code error aligned pc
      (by simp [tag, Emit.valueTag]) (by rfl)

end SszArm.Measure

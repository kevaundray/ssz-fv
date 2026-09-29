import SszArm.CodecDecodeBoundedAbsentReturn

namespace SszArm.Codec.Decode.Bounded

open SszNative

/-- Original-entry full physical contract for the absent-bound branch, including
unread Option payload, raw actual operand preservation, and the exact store frame. -/
theorem program_none_correct (s : ArmState) (base : BitVec 64) (actual : NatOperand)
    (owned : Owned s none actual) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    ∃ t, run 22 s = t ∧ Post s t none actual := by
  let t := absentState s base
  have returned := absent_returned s base actual owned error
  have framed := absent_frame s base actual owned
  have preserved := inputs_preserved owned (result_local_frame (.ok ()) framed)
  refine ⟨t, absent_run s base actual owned code error aligned pc,
    ?_, returned.pc, returned.error, ?_, returned.sp, ?_, ?_, ?_, preserved.1, preserved.2⟩
  · intro used
    simpa [CodecDecode.bounded, Serialize.bounded, Serialize.unchanged]
      using absent_status s base owned.resultBound
  · simp [t, absentState, tagRead, state_simp_rules]
  · intro reg low high
    by_cases eighteen : reg = 18#5
    · subst reg
      simp [t, absentState, restored, tagRead, state_simp_rules]
    · exact returned.registers reg (by bv_omega) high
  · intro reg
    simp [t, absentState, tagRead, state_simp_rules]
  · intro used
    simpa [CodecDecode.bounded, Serialize.bounded, Serialize.unchanged] using framed

end SszArm.Codec.Decode.Bounded

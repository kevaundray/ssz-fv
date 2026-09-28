import SszArm.MeasureBitVectorOwnership

namespace SszArm.Measure.BitVector

open SszNative (NatOperand)
open SszNative.Serialize (Value)

theorem wrong_body (s : ArmState) (base : BitVec 64) (args : Args)
    (cap : NatOperand) (value : Value)
    (owned : Owned s args (.bitVector cap) value) (registers : BodyRegisters s args)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 568#64)
    (tag : r (.GPR 8#5) s = (Emit.valueTag value).setWidth 64)
    (notBits : ∀ bits, value ≠ .bits bits) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args (.bitVector cap) value base := by
  let u := gated s base
  have pre : run 2 s = u := gate_run s base code error pc
  have up : u.program = s.program := gated_program s base
  have ue : read_err u = .None := (gated_error s base).trans error
  have ua : CheckSPAlignment u := by
    simpa [u, gated, CheckSPAlignment, state_simp_rules] using aligned
  have own : Owned u args (.bitVector cap) value := owned.of_local_frame (by
    intro address outside
    simp [u, gated, write_pstate, ArmState.mem_w_eq_mem])
  have measured : outcome u args (.bitVector cap) value =
      SszNative.Serialize.unchanged (arenaOf u args).used (.error .wrongType) := by
    cases value with
    | bits bits => exact False.elim (notBits bits rfl)
    | bool flag | uint flag | bytes flag | seq flag => rfl
    | union selector content => rfl
  have post := Result.wrong_produced base own
    ((gated_register s base 19#5).trans registers.result)
    ((gated_register s base 31#5).trans registers.stack)
    (by rw [measured]; rfl) (by rw [measured]; rfl) (by rw [measured]; rfl) ue
  refine ⟨50, Result.wrongResult u base, ?_, Scalar.prepend_pure post up (gated_memory s base) ?_ ?_⟩
  · rw [show 50 = 2 + 48 by decide, run_plus, pre]
    exact Result.wrong_run u base (code.congr up) ue ua (gated_pc_wrong s base value tag notBits)
  · intro reg member
    exact gated_register s base reg
  · intro reg low high
    rw [gated_vector]

end SszArm.Measure.BitVector

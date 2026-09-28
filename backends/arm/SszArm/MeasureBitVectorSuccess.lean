import SszArm.MeasureBitVectorOwnership

namespace SszArm.Measure.BitVector

open Result
open SszNative (NatOperand)
open SszNative.Serialize (Packed)

private theorem success3312_effect (s : ArmState) :
    p3312.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 20#5) (read_mem_bytes 8 (r (.GPR 21#5) s + 24#64) s) s) := by
  change exec_inst (.LDST (.Reg_unsigned_imm
    { size := 3, V := 0, opc := 1, imm12 := 3, Rn := 21, Rt := 20 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

private theorem success3316_effect (s : ArmState) :
    p3316.effect s = w .PC (r .PC s + 428#64) s := by
  change exec_inst (.BR (.Uncond_branch_imm { op := 0, imm26 := 107 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

private theorem success3744_effect (s : ArmState) :
    p3744.effect s = w .PC (r .PC s + 4#64) (w (.GPR 21#5) 0#64 s) := by
  change exec_inst (.DPR (.Logical_shifted_reg
    { sf := 1, opc := 1, shift := 0, N := 0, Rm := 31, imm6 := 0, Rn := 31, Rd := 21 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

private theorem success3748_effect (s : ArmState) :
    p3748.effect s = w .PC (r .PC s + 396#64) s := by
  change exec_inst (.BR (.Uncond_branch_imm { op := 0, imm26 := 99 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

@[irreducible] def successReady (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 4144#64) (w (.GPR 21#5) 0#64
    (w (.GPR 20#5) (read_mem_bytes 8 (r (.GPR 21#5) s + 24#64) s) s))

theorem success_ready_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 3312#64) : run 4 s = successReady s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base [p3312, p3316, p3744, p3748] s := by
    simp (config := {decide := true, instances := true})
      [Follows, show p3312.offset = 3312 from rfl, show p3316.offset = 3316 from rfl,
       show p3744.offset = 3744 from rfl, show p3748.offset = 3748 from rfl,
       success3312_effect, success3316_effect, success3744_effect,
       state_simp_rules, pc, error, BitVec.add_assoc]
  rw [show 4 = [p3312, p3316, p3744, p3748].length by rfl, runs _ s base code follows]
  simp (config := {decide := true, instances := true})
    [successReady, effect, success3312_effect, success3316_effect,
     success3744_effect, success3748_effect, state_simp_rules,
     pc, BitVec.add_assoc, NatExact.gpr_w_pc]

theorem success_body (s : ArmState) (base : BitVec 64) (args : Args)
    (cap : NatOperand) (bits : Packed)
    (owned : Owned s args (.bitVector cap) (.bits bits)) (registers : BodyRegisters s args)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3312#64) (equal : cap.value = bits.count.toNat) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args (.bitVector cap) (.bits bits) base := by
  let u := successReady s base
  have pre : run 4 s = u := success_ready_run s base code error pc
  have up : u.program = s.program := by simp [u, successReady, state_simp_rules]
  have ue : read_err u = .None := by simpa [u, successReady, state_simp_rules] using error
  have ua : CheckSPAlignment u := by
    simpa (config := {decide := true}) [u, successReady, CheckSPAlignment, state_simp_rules] using aligned
  have uo : r (.GPR 19#5) u = args.result := by
    simpa (config := {decide := true}) [u, successReady, state_simp_rules] using registers.result
  have us : r (.GPR 31#5) u = args.bodySP := by
    simpa (config := {decide := true}) [u, successReady, state_simp_rules] using registers.stack
  have own : Owned u args (.bitVector cap) (.bits bits) := owned.of_local_frame (by
    intro address outside
    simp [u, successReady, ArmState.mem_w_eq_mem])
  have measured : outcome u args (.bitVector cap) (.bits bits) =
      SszNative.Serialize.unchanged (arenaOf u args).used
        (.ok (.small (BitVec.ofNat 64 bits.bytes.size))) := by
    simp [outcome, SszNative.Serialize.measure, equal, SszNative.Serialize.count]
  have post := Result.success_produced base own uo us (.small (BitVec.ofNat 64 bits.bytes.size))
    (by rw [measured]; rfl) (by rw [measured]; rfl) (by rw [measured]; rfl)
    (by simp [u, successReady, NatOperand.pointer, state_simp_rules])
    (by simp [u, successReady, NatOperand.payload, state_simp_rules, registers.value, length_read owned])
    (by trivial) (by trivial) ue
  refine ⟨37, successResult u base, ?_, Scalar.prepend_pure post up ?_ ?_ ?_⟩
  · rw [show 37 = 4 + 33 by decide, run_plus, pre]
    exact success_run u base (code.congr up) ue ua (by simp [u, successReady, state_simp_rules])
  · simp [u, successReady, ArmState.mem_w_eq_mem]
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [u, successReady, state_simp_rules]
  · intro reg low high
    simp [u, successReady, state_simp_rules]

end SszArm.Measure.BitVector

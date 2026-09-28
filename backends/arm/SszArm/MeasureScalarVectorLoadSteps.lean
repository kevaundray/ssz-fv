import SszArm.MeasureScalarByteFinish

namespace SszArm.Measure.Scalar.Bytes

open Result

def p3004 : Op := ⟨3004, 0xaa1f03eb#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 31, imm6 := 0, Rn := 31, Rd := 11 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p3008 : Op := ⟨3008, 0x140000b5#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 181 }), by rfl,
  by simp only [bodyProgram, List.mem_append]; decide⟩

namespace VectorLoadSteps

theorem load2852_effect (s : ArmState) :
    p2852.effect s = w .PC
      (if r (.GPR 9#5) s = 0#64 then r .PC s + 872#64 else r .PC s + 4#64) s := by
  change exec_inst (.BR (.Compare_branch { sf := 1, op := 0, imm19 := 218, Rt := 9 })) s = _
  by_cases zero : r (.GPR 9#5) s = 0#64 <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, zero]

theorem load2856_effect (s : ArmState) :
    p2856.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 10#5) (read_mem_bytes 8 (r (.GPR 8#5) s) s) s) := by
  change exec_inst (.LDST (.Reg_unsigned_imm
    { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 8, Rt := 10 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

theorem load2860_effect (s : ArmState) :
    p2860.effect s = write_pstate (AddWithCarry (r (.GPR 9#5) s) (~~~2#64) 1#1).2
      (w .PC (r .PC s + 4#64) s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 1, op := 1, S := 1, sh := 0, imm12 := 2, Rn := 9, Rd := 31 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem load2864_effect (s : ArmState) :
    p2864.effect s = w .PC
      (if r (.FLAG .C) s = 1#1 then r .PC s + 4#64 else r .PC s + 140#64) s := by
  change exec_inst (.BR (.Cond_branch_imm { imm19 := 35, o0 := 0, cond := 3 })) s = _
  have choices : r (.FLAG .C) s = 0#1 ∨ r (.FLAG .C) s = 1#1 := by bv_omega
  rcases choices with flag | flag <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, flag]

theorem load2868_effect (s : ArmState) :
    p2868.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 11#5) (read_mem_bytes 8 (r (.GPR 8#5) s + 8#64) s) s) := by
  change exec_inst (.LDST (.Reg_unsigned_imm
    { size := 3, V := 0, opc := 1, imm12 := 1, Rn := 8, Rt := 11 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

theorem load2872_effect (s : ArmState) : p2872.effect s = w .PC (r .PC s + 860#64) s := by
  change exec_inst (.BR (.Uncond_branch_imm { op := 0, imm26 := 215 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem load3004_effect (s : ArmState) :
    p3004.effect s = w .PC (r .PC s + 4#64) (w (.GPR 11#5) 0#64 s) := by
  change exec_inst (.DPR (.Logical_shifted_reg
    { sf := 1, opc := 1, shift := 0, N := 0, Rm := 31, imm6 := 0, Rn := 31, Rd := 11 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

theorem load3008_effect (s : ArmState) : p3008.effect s = w .PC (r .PC s + 724#64) s := by
  change exec_inst (.BR (.Uncond_branch_imm { op := 0, imm26 := 181 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem load3724_effect (s : ArmState) :
    p3724.effect s = w .PC (r .PC s + 4#64) (w (.GPR 11#5) 0#64 s) := by
  exact load3004_effect s

theorem load3728_effect (s : ArmState) :
    p3728.effect s = w .PC (r .PC s + 4#64) (w (.GPR 10#5) 0#64 s) := by
  change exec_inst (.DPR (.Logical_shifted_reg
    { sf := 1, opc := 1, shift := 0, N := 0, Rm := 31, imm6 := 0, Rn := 31, Rd := 10 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

end VectorLoadSteps
end SszArm.Measure.Scalar.Bytes

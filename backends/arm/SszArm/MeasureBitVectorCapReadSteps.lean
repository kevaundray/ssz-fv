import SszArm.MeasureBitVectorCapFrame

namespace SszArm.Measure.BitVector

open Result

theorem cap_read2832_effect (s : ArmState) :
    p2832.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 12#5) (read_mem_bytes 8 (r (.GPR 11#5) s) s) s) := by
  change exec_inst (.LDST (.Reg_unsigned_imm
    { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 11, Rt := 12 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

theorem cap_read2836_effect (s : ArmState) :
    p2836.effect s = write_pstate
      (AddWithCarry (r (.GPR 10#5) s) (~~~2#64) 1#1).2
      (w .PC (r .PC s + 4#64) s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 1, op := 1, S := 1, sh := 0, imm12 := 2, Rn := 10, Rd := 31 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem cap_read2840_effect (s : ArmState) :
    p2840.effect s = w .PC
      (if r (.FLAG .C) s = 1#1 then r .PC s + 4#64 else r .PC s + 152#64) s := by
  change exec_inst (.BR (.Cond_branch_imm { imm19 := 38, o0 := 0, cond := 3 })) s = _
  have choices : r (.FLAG .C) s = 0#1 ∨ r (.FLAG .C) s = 1#1 := by bv_omega
  rcases choices with flag | flag <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, flag]

theorem cap_read2844_effect (s : ArmState) :
    p2844.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 11#5) (read_mem_bytes 8 (r (.GPR 11#5) s + 8#64) s) s) := by
  change exec_inst (.LDST (.Reg_unsigned_imm
    { size := 3, V := 0, opc := 1, imm12 := 1, Rn := 11, Rt := 11 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

theorem cap_read2848_effect (s : ArmState) :
    p2848.effect s = w .PC (r .PC s + 148#64) s := by
  change exec_inst (.BR (.Uncond_branch_imm { op := 0, imm26 := 37 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem cap_read2992_effect (s : ArmState) :
    p2992.effect s = w .PC (r .PC s + 4#64) (w (.GPR 11#5) 0#64 s) := by
  change exec_inst (.DPR (.Logical_shifted_reg
    { sf := 1, opc := 1, shift := 0, N := 0, Rm := 31, imm6 := 0, Rn := 31, Rd := 11 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

theorem cap_read2996_effect (s : ArmState) :
    p2996.effect s = w .PC (r .PC s + 4#64) (w (.GPR 10#5) (r (.GPR 12#5) s) s) := by
  change exec_inst (.DPR (.Logical_shifted_reg
    { sf := 1, opc := 1, shift := 0, N := 0, Rm := 12, imm6 := 0, Rn := 31, Rd := 10 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

theorem cap_read3000_effect (s : ArmState) :
    p3000.effect s = w .PC (r .PC s + 268#64) s := by
  change exec_inst (.BR (.Uncond_branch_imm { op := 0, imm26 := 67 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

end SszArm.Measure.BitVector

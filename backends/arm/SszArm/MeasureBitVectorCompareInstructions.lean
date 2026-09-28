import SszArm.MeasureBitVectorFrame

namespace SszArm.Measure.BitVector

open Result

/-- Reduce each accepted literal decoder before simplifying its execution. -/
theorem compare3268_effect (s : ArmState) :
    p3268.effect s = write_pstate
      (AddWithCarry (r (.GPR 11#5) s) (~~~r (.GPR 9#5) s) 1#1).2
      (w .PC (r .PC s + 4#64) s) := by
  change exec_inst (.DPR (.Add_sub_shifted_reg
    { sf := 1, op := 1, S := 1, shift := 0, Rm := 9, imm6 := 0, Rn := 11, Rd := 31 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem compare3272_effect (s : ArmState) :
    p3272.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 31#5) (r (.GPR 31#5) s - 16#64) s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

theorem compare3276_effect (s : ArmState) (aligned : CheckSPAlignment s) :
    p3276.effect s = w .PC (r .PC s + 4#64)
      (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s) := by
  change exec_inst (.LDST (.Reg_unsigned_imm
    { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned, NatExact.store_w]

theorem compare3280_effect (s : ArmState) :
    p3280.effect s = w .PC
      (if r (.FLAG .Z) s = 1#1 then r .PC s + 16#64 else r .PC s + 4#64) s := by
  change exec_inst (.BR (.Cond_branch_imm { imm19 := 4, o0 := 0, cond := 0 })) s = _
  by_cases zero : r (.FLAG .Z) s = 1#1 <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, zero]

theorem compare3284_effect (s : ArmState) :
    p3284.effect s = w .PC (r .PC s + 4#64) (w (.GPR 9#5) 1#64 s) := by
  change exec_inst (.DPI (.Move_wide_imm
    { sf := 0, opc := 2, hw := 0, imm16 := 1, Rd := 9 })) s = _
  have moveOne : BitVec.partInstall 0 16 1#16 0#32 = 1#32 := by decide
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, moveOne, NatExact.gpr_w_pc]

theorem compare3288_effect (s : ArmState) :
    p3288.effect s = write_pstate
      (AddWithCarry ((r (.GPR 9#5) s).setWidth 32) 0#32 0#1).2
      (w .PC (r .PC s + 4#64) s) := by
  change exec_inst (.DPR (.Add_sub_shifted_reg
    { sf := 0, op := 0, S := 1, shift := 0, Rm := 31, imm6 := 0, Rn := 9, Rd := 31 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem compare3292_effect (s : ArmState) :
    p3292.effect s = w .PC (r .PC s + 8#64) s := by
  change exec_inst (.BR (.Uncond_branch_imm { op := 0, imm26 := 2 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem compare3296_effect (s : ArmState) :
    p3296.effect s = write_pstate
      (AddWithCarry (r (.GPR 10#5) s) (~~~r (.GPR 8#5) s) 1#1).2
      (w .PC (r .PC s + 4#64) s) := by
  change exec_inst (.DPR (.Add_sub_shifted_reg
    { sf := 1, op := 1, S := 1, shift := 0, Rm := 8, imm6 := 0, Rn := 10, Rd := 31 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem compare3300_effect (s : ArmState) (aligned : CheckSPAlignment s) :
    p3300.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 31#5) s) s) s) := by
  change exec_inst (.LDST (.Reg_unsigned_imm
    { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned, NatExact.gpr_w_pc]

theorem compare3304_effect (s : ArmState) :
    p3304.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 31#5) (r (.GPR 31#5) s + 16#64) s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

theorem compare3308_effect (s : ArmState) :
    p3308.effect s = w .PC
      (if r (.FLAG .Z) s = 0#1 then r .PC s + 12#64 else r .PC s + 4#64) s := by
  change exec_inst (.BR (.Cond_branch_imm { imm19 := 3, o0 := 0, cond := 1 })) s = _
  have bits : r (.FLAG .Z) s = 0#1 ∨ r (.FLAG .Z) s = 1#1 := by bv_omega
  rcases bits with flag | flag <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, flag]

end SszArm.Measure.BitVector

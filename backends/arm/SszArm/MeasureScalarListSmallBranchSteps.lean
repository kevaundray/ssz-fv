import SszArm.MeasureScalarListSmallFlags

namespace SszArm.Measure.Scalar.Bytes.SmallBranchSteps

open Result

theorem p2008_effect (s : ArmState) :
    p2008.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 31#5) (r (.GPR 31#5) s - 16#64) s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 1, op := 1, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.sub_eq_add_neg, NatExact.gpr_w_pc]

theorem p2028_effect (s : ArmState) :
    p2028.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 31#5) (r (.GPR 31#5) s + 16#64) s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 1, op := 0, S := 0, sh := 0, imm12 := 16, Rn := 31, Rd := 31 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.sub_eq_add_neg, NatExact.gpr_w_pc]

theorem p2040_effect (s : ArmState) :
    p2040.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 31#5) (r (.GPR 31#5) s + 16#64) s) := p2028_effect s

theorem p2012_effect (s : ArmState) (aligned : Aligned (r (.GPR 31#5) s) 4) :
    p2012.effect s = w .PC (r .PC s + 4#64)
      (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s) := by
  change exec_inst (.LDST (.Reg_unsigned_imm
    { size := 3, V := 0, opc := 0, imm12 := 0, Rn := 31, Rt := 9 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned, NatExact.store_w]

theorem p2024_effect (s : ArmState) (aligned : Aligned (r (.GPR 31#5) s) 4) :
    p2024.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 31#5) s) s) s) := by
  change exec_inst (.LDST (.Reg_unsigned_imm
    { size := 3, V := 0, opc := 1, imm12 := 0, Rn := 31, Rt := 9 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned, NatExact.gpr_w_pc]

theorem p2036_effect (s : ArmState) (aligned : Aligned (r (.GPR 31#5) s) 4) :
    p2036.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 31#5) s) s) s) := p2024_effect s aligned

theorem p2016_effect (s : ArmState) :
    p2016.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 9#5) (((r (.GPR 11#5) s).setWidth 32 &&& 1#32).setWidth 64) s) := by
  change exec_inst (.DPI (.Logical_imm
    { sf := 0, opc := 0, N := 0, immr := 0, imms := 0, Rn := 11, Rd := 9 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

theorem p2020_effect (s : ArmState) :
    p2020.effect s = w .PC
      (if (r (.GPR 9#5) s).setWidth 32 = 0#32 then r .PC s + 4#64 else r .PC s + 16#64) s := by
  change exec_inst (.BR (.Compare_branch { sf := 0, op := 1, imm19 := 4, Rt := 9 })) s = _
  by_cases zero : (r (.GPR 9#5) s).setWidth 32 = 0#32 <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, zero]

theorem p2032_effect (s : ArmState) : p2032.effect s = w .PC (r .PC s + 16#64) s := by
  change exec_inst (.BR (.Uncond_branch_imm { op := 0, imm26 := 4 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem p2044_effect (s : ArmState) : p2044.effect s = w .PC (r .PC s + 344#64) s := by
  change exec_inst (.BR (.Uncond_branch_imm { op := 0, imm26 := 86 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

end SszArm.Measure.Scalar.Bytes.SmallBranchSteps

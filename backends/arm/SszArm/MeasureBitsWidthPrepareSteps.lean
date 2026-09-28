import SszArm.MeasureBitsWidthOps

namespace SszArm.Measure.Bits.Width

open Result

theorem prepare1876_effect (s : ArmState) :
    p1876.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 9#5) (r (.GPR 25#5) s >>> (3 : Nat)) s) := by
  change exec_inst (.DPI (.Bitfield
    { sf := 1, opc := 2, N := 1, immr := 3, imms := 63, Rn := 25, Rd := 9 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      UintCodec.uint_and_ones, UintCodec.uint_lsr3_mask, NatExact.gpr_w_pc]

theorem prepare1880_effect (s : ArmState) :
    p1880.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 0#5) (r (.GPR 31#5) s + 120#64) s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 1, op := 0, S := 0, sh := 0, imm12 := 120, Rn := 31, Rd := 0 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

theorem prepare1884_effect (s : ArmState) :
    p1884.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 4#5) (r (.GPR 20#5) s) s) := by
  change exec_inst (.DPR (.Logical_shifted_reg
    { sf := 1, opc := 1, shift := 0, N := 0, Rm := 20, imm6 := 0, Rn := 31, Rd := 4 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

theorem prepare1888_effect (s : ArmState) :
    p1888.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 23#5) (r (.GPR 31#5) s + 120#64) s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 1, op := 0, S := 0, sh := 0, imm12 := 120, Rn := 31, Rd := 23 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

theorem prepare1892_effect (s : ArmState) :
    p1892.effect s = w (.GPR 2#5) (r (.GPR 8#5) s + 1#64)
      (write_pstate (AddWithCarry (r (.GPR 8#5) s) 1#64 0#1).2
        (w .PC (r .PC s + 4#64) s)) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 1, op := 0, S := 1, sh := 0, imm12 := 1, Rn := 8, Rd := 2 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem prepare1896_effect (s : ArmState) :
    p1896.effect s = w .PC
      (if r (.FLAG .C) s = 1#1 then r .PC s + 12#64 else r .PC s + 4#64) s := by
  change exec_inst (.BR (.Cond_branch_imm { imm19 := 3, o0 := 0, cond := 2 })) s = _
  by_cases carry : r (.FLAG .C) s = 1#1 <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, carry]

theorem prepare1900_effect (s : ArmState) :
    p1900.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 3#5) (r (.GPR 9#5) s) s) := by
  change exec_inst (.DPR (.Logical_shifted_reg
    { sf := 1, opc := 1, shift := 0, N := 0, Rm := 9, imm6 := 0, Rn := 31, Rd := 3 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

theorem prepare1904_effect (s : ArmState) :
    p1904.effect s = w .PC (r .PC s + 8#64) s := by
  change exec_inst (.BR (.Uncond_branch_imm { op := 0, imm26 := 2 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem prepare1908_effect (s : ArmState) :
    p1908.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 3#5) (r (.GPR 9#5) s + 1#64) s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 1, op := 0, S := 0, sh := 0, imm12 := 1, Rn := 9, Rd := 3 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

end SszArm.Measure.Bits.Width

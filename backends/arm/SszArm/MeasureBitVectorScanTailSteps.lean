import SszArm.MeasureBitVectorOps

namespace SszArm.Measure.BitVector

open Result

theorem scan_remember_effect (s : ArmState) :
    p632.effect s = w .PC (r .PC s + 4#64) (w (.GPR 12#5) (r (.GPR 13#5) s) s) := by
  change exec_inst (.DPR (.Logical_shifted_reg
    { sf := 1, opc := 1, shift := 0, N := 0, Rm := 13, imm6 := 0, Rn := 31, Rd := 12 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

theorem scan_decrement_effect (s : ArmState) :
    p636.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 13#5) (r (.GPR 13#5) s - 1#64) s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 1, op := 1, S := 0, sh := 0, imm12 := 1, Rn := 13, Rd := 13 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

theorem scan_limb_branch_effect (s : ArmState) :
    p640.effect s = w .PC
      (if r (.GPR 14#5) s = 0#64 then r .PC s + 18446744073709551568#64
       else r .PC s + 4#64) s := by
  change exec_inst (.BR (.Compare_branch
    { sf := 1, op := 0, imm19 := 524276, Rt := 14 })) s = _
  by_cases zero : r (.GPR 14#5) s = 0#64 <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, zero]

end SszArm.Measure.BitVector

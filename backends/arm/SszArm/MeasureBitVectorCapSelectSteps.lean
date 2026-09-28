import SszArm.MeasureBitVectorCapRoute

namespace SszArm.Measure.BitVector

open Result

theorem cap_select644_effect (s : ArmState) :
    p644.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 12#5) (r (.GPR 12#5) s + 1#64) s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 1, op := 0, S := 0, sh := 0, imm12 := 1, Rn := 12, Rd := 12 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

theorem cap_select648_effect (s : ArmState) :
    p648.effect s = write_pstate
      (AddWithCarry (r (.GPR 12#5) s) (~~~3#64) 1#1).2
      (w .PC (r .PC s + 4#64) s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 1, op := 1, S := 1, sh := 0, imm12 := 3, Rn := 12, Rd := 31 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem cap_select652_effect (s : ArmState) :
    p652.effect s = w .PC
      (if r (.FLAG .C) s = 1#1 then r .PC s + 4#64 else r .PC s + 2180#64) s := by
  change exec_inst (.BR (.Cond_branch_imm { imm19 := 545, o0 := 0, cond := 3 })) s = _
  have choices : r (.FLAG .C) s = 0#1 ∨ r (.FLAG .C) s = 1#1 := by bv_omega
  rcases choices with flag | flag <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, flag]

theorem cap_select656_effect (s : ArmState) :
    p656.effect s = w .PC (r .PC s + 2664#64) s := by
  change exec_inst (.BR (.Uncond_branch_imm { op := 0, imm26 := 666 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

end SszArm.Measure.BitVector

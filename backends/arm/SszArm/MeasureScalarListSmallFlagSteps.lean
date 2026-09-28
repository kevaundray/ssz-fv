import SszArm.MeasureScalarListLarge

namespace SszArm.Measure.Scalar.Bytes.SmallFlagSteps

open Result

theorem p1960_effect (s : ArmState) :
    p1960.effect s = write_pstate (AddWithCarry (r (.GPR 20#5) s) (~~~0#64) 1#1).2
      (w .PC (r .PC s + 4#64) s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 1, op := 1, S := 1, sh := 0, imm12 := 0, Rn := 20, Rd := 31 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem p1980_effect (s : ArmState) :
    p1980.effect s = write_pstate (AddWithCarry (r (.GPR 9#5) s) (~~~0#64) 1#1).2
      (w .PC (r .PC s + 4#64) s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 1, op := 1, S := 1, sh := 0, imm12 := 0, Rn := 9, Rd := 31 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem p1964_effect (s : ArmState) :
    p1964.effect s = w .PC
      (if r (.FLAG .Z) s = 1#1 then r .PC s + 4#64 else r .PC s + 12#64) s := by
  change exec_inst (.BR (.Cond_branch_imm { imm19 := 3, o0 := 0, cond := 1 })) s = _
  have choices : r (.FLAG .Z) s = 0#1 ∨ r (.FLAG .Z) s = 1#1 := by bv_omega
  rcases choices with flag | flag <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, flag]

theorem p1984_effect (s : ArmState) :
    p1984.effect s = w .PC
      (if r (.FLAG .Z) s = 1#1 then r .PC s + 4#64 else r .PC s + 12#64) s :=
  p1964_effect s

theorem p1968_effect (s : ArmState) :
    p1968.effect s = w .PC (r .PC s + 4#64) (w (.GPR 10#5) 0#64 s) :=
  ListSteps.p2340_effect s

theorem p1976_effect (s : ArmState) :
    p1976.effect s = w .PC (r .PC s + 4#64) (w (.GPR 10#5) 1#64 s) :=
  ListSteps.p2348_effect s

theorem p1972_effect (s : ArmState) :
    p1972.effect s = w .PC (r .PC s + 8#64) s := ListSteps.p2384_effect s

theorem p1992_effect (s : ArmState) :
    p1992.effect s = w .PC (r .PC s + 8#64) s := ListSteps.p2384_effect s

theorem p1988_effect (s : ArmState) :
    p1988.effect s = w .PC (r .PC s + 4#64) (w (.GPR 11#5) 0#64 s) := by
  change exec_inst (.DPI (.Move_wide_imm
    { sf := 0, opc := 2, hw := 0, imm16 := 0, Rd := 11 })) s = _
  have literal : BitVec.partInstall 0 16 0#16 0#32 = 0#32 := by decide
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, literal, NatExact.gpr_w_pc]

theorem p1996_effect (s : ArmState) :
    p1996.effect s = w .PC (r .PC s + 4#64) (w (.GPR 11#5) 1#64 s) := by
  change exec_inst (.DPI (.Move_wide_imm
    { sf := 0, opc := 2, hw := 0, imm16 := 1, Rd := 11 })) s = _
  have literal : BitVec.partInstall 0 16 1#16 0#32 = 1#32 := by decide
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, literal, NatExact.gpr_w_pc]

theorem p2000_effect (s : ArmState) :
    p2000.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 11#5) (((r (.GPR 11#5) s).setWidth 32 ^^^
        (r (.GPR 10#5) s).setWidth 32).setWidth 64) s) := by
  change exec_inst (.DPR (.Logical_shifted_reg
    { sf := 0, opc := 2, shift := 0, N := 0, Rm := 10, imm6 := 0, Rn := 11, Rd := 11 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

theorem p2004_effect (s : ArmState) :
    p2004.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 10#5) (if r (.FLAG .Z) s = 1#1
        then ((r (.GPR 10#5) s).setWidth 32).setWidth 64 else 0#64) s) := by
  change exec_inst (.DPR (.Conditional_select
    { sf := 0, op := 0, S := 0, Rm := 10, cond := 1, op2 := 0, Rn := 31, Rd := 10 })) s = _
  have choices : r (.FLAG .Z) s = 0#1 ∨ r (.FLAG .Z) s = 1#1 := by bv_omega
  rcases choices with flag | flag <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, flag, NatExact.gpr_w_pc]

end SszArm.Measure.Scalar.Bytes.SmallFlagSteps

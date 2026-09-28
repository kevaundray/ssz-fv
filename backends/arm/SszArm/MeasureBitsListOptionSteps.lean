import SszArm.MeasureBitsListOps
import SszArm.MeasureBitVectorCompareInstructions

namespace SszArm.Measure.Bits.ListEntry

open Result

theorem option716_effect (s : ArmState) :
    p716.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 31#5) (r (.GPR 31#5) s - 16#64) s) :=
  BitVector.compare3272_effect s

theorem option720_effect (s : ArmState) (aligned : CheckSPAlignment s) :
    p720.effect s = w .PC (r .PC s + 4#64)
      (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s) :=
  BitVector.compare3276_effect s aligned

theorem option724_effect (s : ArmState) :
    p724.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 9#5) (((r (.GPR 8#5) s).setWidth 32 &&& 1#32).setWidth 64) s) := by
  change exec_inst (.DPI (.Logical_imm
    { sf := 0, opc := 0, N := 0, immr := 0, imms := 0, Rn := 8, Rd := 9 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

theorem option728_effect (s : ArmState) :
    p728.effect s = w .PC
      (if (r (.GPR 9#5) s).setWidth 32 = 0#32 then r .PC s + 4#64 else r .PC s + 16#64) s := by
  change exec_inst (.BR (.Compare_branch { sf := 0, op := 1, imm19 := 4, Rt := 9 })) s = _
  by_cases zero : (r (.GPR 9#5) s).setWidth 32 = 0#32 <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, zero]

theorem option732_effect (s : ArmState) (aligned : CheckSPAlignment s) :
    p732.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 31#5) s) s) s) :=
  BitVector.compare3300_effect s aligned

theorem option736_effect (s : ArmState) :
    p736.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 31#5) (r (.GPR 31#5) s + 16#64) s) :=
  BitVector.compare3304_effect s

theorem option740_effect (s : ArmState) :
    p740.effect s = w .PC (r .PC s + 16#64) s := by
  change exec_inst (.BR (.Uncond_branch_imm { op := 0, imm26 := 4 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem option744_effect (s : ArmState) (aligned : CheckSPAlignment s) :
    p744.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 31#5) s) s) s) :=
  option732_effect s aligned

theorem option748_effect (s : ArmState) :
    p748.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 31#5) (r (.GPR 31#5) s + 16#64) s) :=
  option736_effect s

theorem option752_effect (s : ArmState) :
    p752.effect s = w .PC (r .PC s + 960#64) s := by
  change exec_inst (.BR (.Uncond_branch_imm { op := 0, imm26 := 240 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem option756_effect (s : ArmState) :
    p756.effect s = w .PC (r .PC s + 1096#64) s := by
  change exec_inst (.BR (.Uncond_branch_imm { op := 0, imm26 := 274 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem option1584_effect (s : ArmState) :
    p1584.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 31#5) (r (.GPR 31#5) s - 16#64) s) := option716_effect s

theorem option1588_effect (s : ArmState) (aligned : CheckSPAlignment s) :
    p1588.effect s = w .PC (r .PC s + 4#64)
      (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s) := option720_effect s aligned

theorem option1592_effect (s : ArmState) :
    p1592.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 9#5) (((r (.GPR 8#5) s).setWidth 32 &&& 1#32).setWidth 64) s) := option724_effect s

theorem option1596_effect (s : ArmState) :
    p1596.effect s = w .PC
      (if (r (.GPR 9#5) s).setWidth 32 = 0#32 then r .PC s + 16#64 else r .PC s + 4#64) s := by
  change exec_inst (.BR (.Compare_branch { sf := 0, op := 0, imm19 := 4, Rt := 9 })) s = _
  by_cases zero : (r (.GPR 9#5) s).setWidth 32 = 0#32 <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, zero]

theorem option1600_effect (s : ArmState) (aligned : CheckSPAlignment s) :
    p1600.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 31#5) s) s) s) := option732_effect s aligned

theorem option1604_effect (s : ArmState) :
    p1604.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 31#5) (r (.GPR 31#5) s + 16#64) s) := option736_effect s

theorem option1608_effect (s : ArmState) :
    p1608.effect s = w .PC (r .PC s + 16#64) s := option740_effect s

theorem option1612_effect (s : ArmState) (aligned : CheckSPAlignment s) :
    p1612.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 31#5) s) s) s) := option732_effect s aligned

theorem option1616_effect (s : ArmState) :
    p1616.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 31#5) (r (.GPR 31#5) s + 16#64) s) := option736_effect s

theorem option1620_effect (s : ArmState) :
    p1620.effect s = w .PC (r .PC s + 232#64) s := by
  change exec_inst (.BR (.Uncond_branch_imm { op := 0, imm26 := 58 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem option1624_effect (s : ArmState) :
    p1624.effect s = w .PC (r .PC s + 88#64) s := by
  change exec_inst (.BR (.Uncond_branch_imm { op := 0, imm26 := 22 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

end SszArm.Measure.Bits.ListEntry

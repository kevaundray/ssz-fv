import SszArm.MeasureResultFields

namespace SszArm.Measure.Scalar

open Result

def p760 : Op := ⟨760, 0x350062e8#32,
  .BR (.Compare_branch { sf := 0, op := 1, imm19 := 791, Rt := 8 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p764 : Op := ⟨764, 0xaa1f03f5#32,
  .DPR (.Logical_shifted_reg { sf := 1, opc := 1, shift := 0, N := 0, Rm := 31, imm6 := 0, Rn := 31, Rd := 21 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p768 : Op := ⟨768, 0x52800034#32,
  .DPI (.Move_wide_imm { sf := 0, opc := 2, hw := 0, imm16 := 1, Rd := 20 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩
def p772 : Op := ⟨772, 0x1400034b#32,
  .BR (.Uncond_branch_imm { op := 0, imm26 := 843 }), by rfl, by simp only [bodyProgram, List.mem_append]; decide⟩

@[irreducible] def boolReady (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 4144#64) (w (.GPR 20#5) 1#64 (w (.GPR 21#5) 0#64 s))

theorem bool_ready_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 760#64) (tag : (r (.GPR 8#5) s).setWidth 32 = 0#32) :
    run 4 s = boolReady s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base [p760, p764, p768, p772] s := by
    simp (config := {decide := true, instances := true})
      [Follows, p760, p764, p768, p772, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, pc, error, tag, BitVec.add_assoc]
  rw [show 4 = [p760, p764, p768, p772].length by rfl, runs _ s base code follows]
  simp (config := {decide := true, instances := true})
    [effect, p760, p764, p768, p772, Op.effect, exec_inst, boolReady,
     state_simp_rules, bitvec_rules, minimal_theory, pc, tag, BitVec.add_assoc,
     NatExact.gpr_w_pc, w_of_w_shadow]

theorem bool_wrong_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 760#64) (tag : (r (.GPR 8#5) s).setWidth 32 ≠ 0#32) :
    run 1 s = w .PC (base + 3924#64) s := by
  have follows : Follows base [p760] s := ⟨error, pc, trivial⟩
  rw [show 1 = [p760].length by rfl, runs _ s base code follows]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, p760, Op.effect, exec_inst, state_simp_rules, bitvec_rules,
     minimal_theory, pc, tag, BitVec.add_assoc]

end SszArm.Measure.Scalar

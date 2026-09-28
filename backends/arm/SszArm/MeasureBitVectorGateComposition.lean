import SszArm.MeasureBitVectorBranchSteps

namespace SszArm.Measure.BitVector

open Result

@[irreducible] def gateStage (s : ArmState) (base : BitVec 64) (flags : PState) : ArmState :=
  w .PC (base + 572#64) (write_pstate flags s)

@[simp] theorem gateStage_program (s : ArmState) (base : BitVec 64) (flags : PState) :
    (gateStage s base flags).program = s.program := by
  simp [gateStage, state_simp_rules]

@[simp] theorem gateStage_error (s : ArmState) (base : BitVec 64) (flags : PState) :
    read_err (gateStage s base flags) = read_err s := by
  simp [gateStage, state_simp_rules]

@[simp] theorem gateStage_pc (s : ArmState) (base : BitVec 64) (flags : PState) :
    r .PC (gateStage s base flags) = base + 572#64 := by
  simp only [gateStage, r_of_w_same]

@[simp] theorem gateStage_zero (s : ArmState) (base : BitVec 64) (flags : PState) :
    r (.FLAG .Z) (gateStage s base flags) = flags.z := by
  simp (disch := decide) only [gateStage, write_pstate, r_of_w_different, r_of_w_same]

theorem gateStage_compare (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 568#64) :
    p568.effect s = gateStage s base
      (AddWithCarry ((r (.GPR 8#5) s).setWidth 32) (~~~3#32) 1#1).2 := by
  rw [gate_compare_effect]
  unfold gateStage
  apply congrArg (fun nextPC => w .PC nextPC
    (write_pstate (AddWithCarry ((r (.GPR 8#5) s).setWidth 32) (~~~3#32) 1#1).2 s))
  change r .PC s = _ at pc
  rw [pc]
  bv_omega

theorem gateStage_branch (s : ArmState) (base : BitVec 64) (flags : PState) :
    p572.effect (gateStage s base flags) =
      w .PC (if flags.z = 1#1 then base + 576#64 else base + 3924#64) (write_pstate flags s) := by
  rw [gate_branch_effect, gateStage_zero, gateStage_pc]
  have fallthrough : base + 572#64 + 4#64 = base + 576#64 := by bv_omega
  have target : base + 572#64 + 3352#64 = base + 3924#64 := by bv_omega
  rw [fallthrough, target]
  unfold gateStage
  exact w_of_w_shadow

end SszArm.Measure.BitVector

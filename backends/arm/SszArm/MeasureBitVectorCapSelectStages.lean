import SszArm.MeasureBitVectorCapSelectSteps

namespace SszArm.Measure.BitVector

open Result

private theorem select_flags_pc (s : ArmState) (flags : PState) (nextPC : BitVec 64) :
    write_pstate flags (w .PC nextPC s) = w .PC nextPC (write_pstate flags s) := by
  simp only [write_pstate, w, write_base_pc, write_base_flag]

@[irreducible] def selectAdded (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 648#64) (w (.GPR 12#5) (r (.GPR 12#5) s + 1#64) s)

@[irreducible] def selectMarked (s : ArmState) (base : BitVec 64) (flags : PState) : ArmState :=
  w .PC (base + 652#64)
    (write_pstate flags (w (.GPR 12#5) (r (.GPR 12#5) s + 1#64) s))

@[irreducible] def selectBranched (s : ArmState) (base : BitVec 64) (flags : PState) : ArmState :=
  w .PC (if flags.c = 1#1 then base + 656#64 else base + 2832#64)
    (write_pstate flags (w (.GPR 12#5) (r (.GPR 12#5) s + 1#64) s))

@[irreducible] def selectJumped (s : ArmState) (base : BitVec 64) (flags : PState) : ArmState :=
  w .PC (base + 3320#64)
    (write_pstate flags (w (.GPR 12#5) (r (.GPR 12#5) s + 1#64) s))

@[simp] theorem selectAdded_program (s : ArmState) (base : BitVec 64) :
    (selectAdded s base).program = s.program := by
  simp [selectAdded, state_simp_rules]

@[simp] theorem selectAdded_error (s : ArmState) (base : BitVec 64) :
    read_err (selectAdded s base) = read_err s := by
  simp [selectAdded, state_simp_rules]

@[simp] theorem selectAdded_pc (s : ArmState) (base : BitVec 64) :
    r .PC (selectAdded s base) = base + 648#64 := by
  simp only [selectAdded, r_of_w_same]

@[simp] theorem selectAdded_value (s : ArmState) (base : BitVec 64) :
    r (.GPR 12#5) (selectAdded s base) = r (.GPR 12#5) s + 1#64 := by
  simp [selectAdded, state_simp_rules]

@[simp] theorem selectMarked_program (s : ArmState) (base : BitVec 64) (flags : PState) :
    (selectMarked s base flags).program = s.program := by
  simp [selectMarked, state_simp_rules]

@[simp] theorem selectMarked_error (s : ArmState) (base : BitVec 64) (flags : PState) :
    read_err (selectMarked s base flags) = read_err s := by
  simp [selectMarked, state_simp_rules]

@[simp] theorem selectMarked_pc (s : ArmState) (base : BitVec 64) (flags : PState) :
    r .PC (selectMarked s base flags) = base + 652#64 := by
  simp only [selectMarked, r_of_w_same]

@[simp] theorem selectMarked_carry (s : ArmState) (base : BitVec 64) (flags : PState) :
    r (.FLAG .C) (selectMarked s base flags) = flags.c := by
  simp [selectMarked, state_simp_rules]

@[simp] theorem selectBranched_program (s : ArmState) (base : BitVec 64) (flags : PState) :
    (selectBranched s base flags).program = s.program := by
  simp [selectBranched, state_simp_rules]

@[simp] theorem selectBranched_error (s : ArmState) (base : BitVec 64) (flags : PState) :
    read_err (selectBranched s base flags) = read_err s := by
  simp [selectBranched, state_simp_rules]

@[simp] theorem selectBranched_pc (s : ArmState) (base : BitVec 64) (flags : PState) :
    r .PC (selectBranched s base flags) =
      if flags.c = 1#1 then base + 656#64 else base + 2832#64 := by
  simp only [selectBranched, r_of_w_same]

theorem selectAdded_add (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 644#64) : p644.effect s = selectAdded s base := by
  change r .PC s = _ at pc
  rw [cap_select644_effect, pc]
  have nextPC : base + 644#64 + 4#64 = base + 648#64 := by bv_omega
  rw [nextPC]
  simp only [selectAdded]

theorem selectAdded_compare (s : ArmState) (base : BitVec 64) :
    p648.effect (selectAdded s base) = selectMarked s base
      (AddWithCarry (r (.GPR 12#5) s + 1#64) (~~~3#64) 1#1).2 := by
  rw [cap_select648_effect, selectAdded_value, selectAdded_pc]
  have nextPC : base + 648#64 + 4#64 = base + 652#64 := by bv_omega
  rw [nextPC]
  unfold selectAdded
  rw [w_of_w_shadow, select_flags_pc]
  simp only [selectMarked]

theorem selectMarked_branch (s : ArmState) (base : BitVec 64) (flags : PState) :
    p652.effect (selectMarked s base flags) = selectBranched s base flags := by
  rw [cap_select652_effect, selectMarked_carry, selectMarked_pc]
  have nextPC : base + 652#64 + 4#64 = base + 656#64 := by bv_omega
  have targetPC : base + 652#64 + 2180#64 = base + 2832#64 := by bv_omega
  rw [nextPC, targetPC]
  unfold selectMarked selectBranched
  exact w_of_w_shadow

theorem selectBranched_jump (s : ArmState) (base : BitVec 64) (flags : PState)
    (taken : flags.c = 1#1) :
    p656.effect (selectBranched s base flags) = selectJumped s base flags := by
  rw [cap_select656_effect, selectBranched_pc]
  simp only [taken, ↓reduceIte]
  have targetPC : base + 656#64 + 2664#64 = base + 3320#64 := by bv_omega
  rw [targetPC]
  unfold selectBranched selectJumped
  exact w_of_w_shadow

theorem select_three_steps (s a b c : ArmState) (first : stepi s = a)
    (second : stepi a = b) (third : stepi b = c) : run 3 s = c := by
  change stepi (stepi (stepi s)) = c
  exact (congrArg (fun state => stepi (stepi state)) first).trans
    ((congrArg stepi second).trans third)

end SszArm.Measure.BitVector

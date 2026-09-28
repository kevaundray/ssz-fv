import SszArm.MeasureBitsWidthPrepareSteps

namespace SszArm.Measure.Bits.Width

open Result

private theorem prepare_flags_pc (s : ArmState) (flags : PState) (pc : BitVec 64) :
    write_pstate flags (w .PC pc s) = w .PC pc (write_pstate flags s) := by
  simp only [write_pstate, w, write_base_pc, write_base_flag]

private theorem prepare_gpr_flags (s : ArmState) (flags : PState)
    (reg : BitVec 5) (value : BitVec 64) :
    w (.GPR reg) value (write_pstate flags s) =
      write_pstate flags (w (.GPR reg) value s) := by
  simp only [write_pstate, w, write_base_gpr, write_base_flag]

@[irreducible] def prepareRegisters (s : ArmState) : ArmState :=
  w (.GPR 23#5) (r (.GPR 31#5) s + 120#64)
    (w (.GPR 4#5) (r (.GPR 20#5) s)
      (w (.GPR 0#5) (r (.GPR 31#5) s + 120#64)
        (w (.GPR 9#5) (r (.GPR 25#5) s >>> (3 : Nat)) s)))

@[irreducible] def prepareArguments (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 1892#64) (prepareRegisters s)

@[irreducible] def prepareMarked (s : ArmState) (base : BitVec 64) (flags : PState) : ArmState :=
  w .PC (base + 1896#64)
    (write_pstate flags (w (.GPR 2#5) (r (.GPR 8#5) s + 1#64) (prepareRegisters s)))

@[irreducible] def prepareBranched (s : ArmState) (base : BitVec 64) (flags : PState) : ArmState :=
  w .PC (if flags.c = 1#1 then base + 1908#64 else base + 1900#64)
    (write_pstate flags (w (.GPR 2#5) (r (.GPR 8#5) s + 1#64) (prepareRegisters s)))

@[simp] theorem prepareArguments_pc (s : ArmState) (base : BitVec 64) :
    r .PC (prepareArguments s base) = base + 1892#64 := by
  simp only [prepareArguments, r_of_w_same]

@[simp] theorem prepareArguments_eight (s : ArmState) (base : BitVec 64) :
    r (.GPR 8#5) (prepareArguments s base) = r (.GPR 8#5) s := by
  simp (config := {decide := true}) [prepareArguments, prepareRegisters, state_simp_rules]

@[simp] theorem prepareArguments_program (s : ArmState) (base : BitVec 64) :
    (prepareArguments s base).program = s.program := by
  simp [prepareArguments, prepareRegisters, state_simp_rules]

@[simp] theorem prepareArguments_error (s : ArmState) (base : BitVec 64) :
    read_err (prepareArguments s base) = read_err s := by
  simp [prepareArguments, prepareRegisters, state_simp_rules]

@[simp] theorem prepareMarked_pc (s : ArmState) (base : BitVec 64) (flags : PState) :
    r .PC (prepareMarked s base flags) = base + 1896#64 := by
  simp only [prepareMarked, r_of_w_same]

@[simp] theorem prepareMarked_carry (s : ArmState) (base : BitVec 64) (flags : PState) :
    r (.FLAG .C) (prepareMarked s base flags) = flags.c := by
  simp [prepareMarked, state_simp_rules]

@[simp] theorem prepareMarked_program (s : ArmState) (base : BitVec 64) (flags : PState) :
    (prepareMarked s base flags).program = s.program := by
  simp [prepareMarked, prepareRegisters, state_simp_rules]

@[simp] theorem prepareMarked_error (s : ArmState) (base : BitVec 64) (flags : PState) :
    read_err (prepareMarked s base flags) = read_err s := by
  simp [prepareMarked, prepareRegisters, state_simp_rules]

theorem prepareArguments_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 1876#64) : run 4 s = prepareArguments s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base [p1876, p1880, p1884, p1888] s := by
    simp (config := {decide := true, instances := true})
      [Follows, prepare1876_effect, prepare1880_effect, prepare1884_effect,
        prepare1888_effect, state_simp_rules, error, pc, BitVec.add_assoc]
    all_goals simp [p1876, p1880, p1884, p1888]
  rw [show 4 = [p1876, p1880, p1884, p1888].length by rfl,
    runs _ s base code follows]
  simp (config := {decide := true, instances := true})
    [effect, prepare1876_effect, prepare1880_effect, prepare1884_effect,
      prepare1888_effect, prepareArguments, prepareRegisters, state_simp_rules,
      NatExact.gpr_w_pc, pc, BitVec.add_assoc]

theorem prepareArguments_add (s : ArmState) (base : BitVec 64) :
    p1892.effect (prepareArguments s base) = prepareMarked s base
      (AddWithCarry (r (.GPR 8#5) s) 1#64 0#1).2 := by
  rw [prepare1892_effect, prepareArguments_eight, prepareArguments_pc]
  have nextPC : base + 1892#64 + 4#64 = base + 1896#64 := by bv_omega
  rw [nextPC]
  simp only [prepareArguments, w_of_w_shadow, prepare_gpr_flags,
    NatExact.gpr_w_pc, prepare_flags_pc, prepareMarked]

theorem prepareMarked_branch (s : ArmState) (base : BitVec 64) (flags : PState) :
    p1896.effect (prepareMarked s base flags) = prepareBranched s base flags := by
  rw [prepare1896_effect, prepareMarked_carry, prepareMarked_pc]
  have taken : base + 1896#64 + 12#64 = base + 1908#64 := by bv_omega
  have notTaken : base + 1896#64 + 4#64 = base + 1900#64 := by bv_omega
  rw [taken, notTaken]
  simp only [prepareMarked, prepareBranched, w_of_w_shadow]

theorem prepare_two_steps (s t u : ArmState) (first : stepi s = t)
    (second : stepi t = u) : run 2 s = u := by
  change stepi (stepi s) = u
  exact (congrArg stepi first).trans second

end SszArm.Measure.Bits.Width

import SszArm.MeasureBitsListCompareSteps

namespace SszArm.Measure.Bits.ListEntry

open Result

private theorem list_compare_flags_pc (s : ArmState) (flags : PState) (nextPC : BitVec 64) :
    write_pstate flags (w .PC nextPC s) = w .PC nextPC (write_pstate flags s) := by
  simp only [write_pstate, w, write_base_pc, write_base_flag]

@[irreducible] def listCompareExtended (s : ArmState) (base : BitVec 64) (value : BitVec 32) : ArmState :=
  w .PC (base + 1736#64) (w (.GPR 8#5) (value.setWidth 64) s)

@[irreducible] def listCompareMarked (s : ArmState) (base : BitVec 64)
    (value : BitVec 32) (flags : PState) : ArmState :=
  w .PC (base + 1740#64) (write_pstate flags (w (.GPR 8#5) (value.setWidth 64) s))

@[simp] theorem listCompareExtended_program (s : ArmState) (base : BitVec 64) (value : BitVec 32) :
    (listCompareExtended s base value).program = s.program := by
  simp [listCompareExtended, state_simp_rules]

@[simp] theorem listCompareExtended_error (s : ArmState) (base : BitVec 64) (value : BitVec 32) :
    read_err (listCompareExtended s base value) = read_err s := by
  simp [listCompareExtended, state_simp_rules]

@[simp] theorem listCompareExtended_pc (s : ArmState) (base : BitVec 64) (value : BitVec 32) :
    r .PC (listCompareExtended s base value) = base + 1736#64 := by
  simp only [listCompareExtended, r_of_w_same]

@[simp] theorem listCompareExtended_value (s : ArmState) (base : BitVec 64) (value : BitVec 32) :
    (r (.GPR 8#5) (listCompareExtended s base value)).setWidth 32 = value := by
  simp [listCompareExtended, state_simp_rules, bitvec_rules]

@[simp] theorem listCompareMarked_program (s : ArmState) (base : BitVec 64)
    (value : BitVec 32) (flags : PState) :
    (listCompareMarked s base value flags).program = s.program := by
  simp [listCompareMarked, state_simp_rules]

@[simp] theorem listCompareMarked_error (s : ArmState) (base : BitVec 64)
    (value : BitVec 32) (flags : PState) :
    read_err (listCompareMarked s base value flags) = read_err s := by
  simp [listCompareMarked, state_simp_rules]

@[simp] theorem listCompareMarked_pc (s : ArmState) (base : BitVec 64)
    (value : BitVec 32) (flags : PState) :
    r .PC (listCompareMarked s base value flags) = base + 1740#64 := by
  simp only [listCompareMarked, r_of_w_same]

@[simp] theorem listCompareMarked_negative (s : ArmState) (base : BitVec 64)
    (value : BitVec 32) (flags : PState) :
    r (.FLAG .N) (listCompareMarked s base value flags) = flags.n := by
  simp [listCompareMarked, state_simp_rules]

@[simp] theorem listCompareMarked_overflow (s : ArmState) (base : BitVec 64)
    (value : BitVec 32) (flags : PState) :
    r (.FLAG .V) (listCompareMarked s base value flags) = flags.v := by
  simp [listCompareMarked, state_simp_rules]

theorem listCompareExtended_extend (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 1732#64) :
    p1732.effect s = listCompareExtended s base (((r (.GPR 0#5) s).setWidth 8).signExtend 32) := by
  change r .PC s = _ at pc
  rw [list_compare_extend_effect, pc]
  have nextPC : base + 1732#64 + 4#64 = base + 1736#64 := by bv_omega
  rw [nextPC]
  simp only [listCompareExtended]

theorem listCompareExtended_compare (s : ArmState) (base : BitVec 64) (value : BitVec 32) :
    p1736.effect (listCompareExtended s base value) =
      listCompareMarked s base value (AddWithCarry value (~~~1#32) 1#1).2 := by
  rw [list_compare_flags_effect, listCompareExtended_value, listCompareExtended_pc]
  have nextPC : base + 1736#64 + 4#64 = base + 1740#64 := by bv_omega
  rw [nextPC]
  unfold listCompareExtended
  rw [list_compare_flags_pc, w_of_w_shadow]
  simp only [listCompareMarked]

theorem listCompareMarked_branch (s : ArmState) (base : BitVec 64)
    (value : BitVec 32) (flags : PState) :
    p1740.effect (listCompareMarked s base value flags) =
      w .PC (if flags.n = flags.v then base + 1744#64 else base + 1852#64)
        (write_pstate flags (w (.GPR 8#5) (value.setWidth 64) s)) := by
  rw [list_compare_branch_effect, listCompareMarked_negative,
    listCompareMarked_overflow, listCompareMarked_pc]
  have nextPC : base + 1740#64 + 4#64 = base + 1744#64 := by bv_omega
  have targetPC : base + 1740#64 + 112#64 = base + 1852#64 := by bv_omega
  rw [nextPC, targetPC]
  unfold listCompareMarked
  exact w_of_w_shadow

theorem list_compare_three_steps (s a b c : ArmState) (first : stepi s = a)
    (second : stepi a = b) (third : stepi b = c) : run 3 s = c := by
  change stepi (stepi (stepi s)) = c
  exact (congrArg (fun state => stepi (stepi state)) first).trans
    ((congrArg stepi second).trans third)

end SszArm.Measure.Bits.ListEntry

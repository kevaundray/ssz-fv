import SszArm.MeasureBitsListCompareStages

namespace SszArm.Measure.Bits.ListEntry

open Result

@[irreducible] def compareReady (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 1728#64)
    (w (.GPR 3#5) (r (.GPR 23#5) s)
      (w (.GPR 2#5) (r (.GPR 22#5) s)
        (w (.GPR 1#5) (r (.GPR 24#5) s)
          (w (.GPR 0#5) (r (.GPR 21#5) s) s))))

theorem compare_setup_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 1712#64) : run 4 s = compareReady s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base [p1712, p1716, p1720, p1724] s := by
    simp (config := {decide := true, instances := true})
      [Follows, p1712, p1716, p1720, p1724, Op.effect, exec_inst,
        state_simp_rules, bitvec_rules, minimal_theory, error, pc, BitVec.add_assoc]
  rw [show 4 = [p1712, p1716, p1720, p1724].length by rfl, runs _ s base code follows]
  simp (config := {decide := true, instances := true})
    [compareReady, effect, p1712, p1716, p1720, p1724, Op.effect, exec_inst,
      state_simp_rules, bitvec_rules, minimal_theory, pc, BitVec.add_assoc,
      NatExact.gpr_w_pc, w_of_w_shadow]

@[irreducible] def compared (order : Ordering) (s : ArmState) (base : BitVec 64) : ArmState :=
  let signed := (SszNative.NatABI.orderingByte order).signExtend 32
  w .PC (base + if order = .gt then 1744#64 else 1852#64)
    (write_pstate (AddWithCarry signed (~~~1#32) 1#1).2
      (w (.GPR 8#5) (signed.setWidth 64) s))

theorem compare_branch_run (order : Ordering) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 1732#64)
    (byte : (r (.GPR 0#5) s).setWidth 8 = SszNative.NatABI.orderingByte order) :
    run 3 s = compared order s base := by
  let signed := (SszNative.NatABI.orderingByte order).signExtend 32
  let flags := (AddWithCarry signed (~~~1#32) 1#1).2
  have extended : p1732.effect s = listCompareExtended s base signed := by
    rw [listCompareExtended_extend s base pc, byte]
  have first : stepi s = listCompareExtended s base signed :=
    (Op.step p1732 s base code error pc).trans extended
  have second : stepi (listCompareExtended s base signed) = listCompareMarked s base signed flags :=
    (Op.step p1736 _ base (code.congr (listCompareExtended_program s base signed))
      ((listCompareExtended_error s base signed).trans error)
      (listCompareExtended_pc s base signed)).trans (listCompareExtended_compare s base signed)
  have destination :
      (if flags.n = flags.v then base + 1744#64 else base + 1852#64) =
        base + (if order = .gt then 1744#64 else 1852#64) := by
    have choice : (flags.n = flags.v) ↔ order = .gt := list_compare_ordering_flags order
    by_cases greater : order = .gt
    · have equal := choice.mpr greater
      simp only [equal, greater, ↓reduceIte]
    · have unequal : flags.n ≠ flags.v := fun equal => greater (choice.mp equal)
      simp only [unequal, greater, ↓reduceIte]
  have third : stepi (listCompareMarked s base signed flags) = compared order s base := by
    calc
      _ = p1740.effect (listCompareMarked s base signed flags) :=
        Op.step p1740 _ base (code.congr (listCompareMarked_program s base signed flags))
          ((listCompareMarked_error s base signed flags).trans error)
          (listCompareMarked_pc s base signed flags)
      _ = w .PC (if flags.n = flags.v then base + 1744#64 else base + 1852#64)
          (write_pstate flags (w (.GPR 8#5) (signed.setWidth 64) s)) :=
        listCompareMarked_branch s base signed flags
      _ = compared order s base := by
        rw [destination]
        unfold compared
        rfl
  exact list_compare_three_steps s _ _ _ first second third

@[simp] theorem compared_program (order : Ordering) (s : ArmState) (base : BitVec 64) :
    (compared order s base).program = s.program := by simp [compared, state_simp_rules]
@[simp] theorem compared_error (order : Ordering) (s : ArmState) (base : BitVec 64) :
    read_err (compared order s base) = read_err s := by simp [compared, state_simp_rules]
@[simp] theorem compared_vector (order : Ordering) (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (compared order s base) = r (.SFP reg) s := by simp [compared, state_simp_rules]
@[simp] theorem compared_memory (order : Ordering) (s : ArmState) (base : BitVec 64) :
    (compared order s base).mem = s.mem := by simp [compared, state_simp_rules]

theorem compared_register (order : Ordering) (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (unchanged : reg ≠ 8#5) : r (.GPR reg) (compared order s base) = r (.GPR reg) s := by
  simp [compared, state_simp_rules, unchanged]

theorem compared_pc (order : Ordering) (s : ArmState) (base : BitVec 64) :
    read_pc (compared order s base) =
      if order = .gt then base + 1744#64 else base + 1852#64 := by
  cases order <;> simp [compared, state_simp_rules]

end SszArm.Measure.Bits.ListEntry

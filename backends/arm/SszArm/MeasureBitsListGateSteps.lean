import SszArm.MeasureBitsListOps

namespace SszArm.Measure.Bits.ListEntry

open Result

private theorem list_gate_compare_effect (s : ArmState) :
    p1248.effect s = w .PC (r .PC s + 4#64)
      (write_pstate (AddWithCarry ((r (.GPR 8#5) s).setWidth 32) (~~~3#32) 1#1).2 s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 0, op := 1, S := 1, sh := 0, imm12 := 3, Rn := 8, Rd := 31 })) s = _
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    cases field <;>
      simp (config := {decide := true, instances := true})
        [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]
    all_goals cases ‹PFlag› <;> simp [state_simp_rules]
  · simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]
  · intro bytes address
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

@[irreducible] def listGateStage (s : ArmState) (nextPC : BitVec 64) (flags : PState) : ArmState :=
  w .PC nextPC (write_pstate flags s)

@[simp] theorem listGateStage_program (s : ArmState) (nextPC : BitVec 64) (flags : PState) :
    (listGateStage s nextPC flags).program = s.program := by
  simp [listGateStage, state_simp_rules]

@[simp] theorem listGateStage_error (s : ArmState) (nextPC : BitVec 64) (flags : PState) :
    read_err (listGateStage s nextPC flags) = read_err s := by
  simp [listGateStage, state_simp_rules]

@[simp] theorem listGateStage_pc (s : ArmState) (nextPC : BitVec 64) (flags : PState) :
    r .PC (listGateStage s nextPC flags) = nextPC := by
  simp only [listGateStage, r_of_w_same]

@[simp] theorem listGateStage_zero (s : ArmState) (nextPC : BitVec 64) (flags : PState) :
    r (.FLAG .Z) (listGateStage s nextPC flags) = flags.z := by
  simp (disch := decide) only [listGateStage, write_pstate, r_of_w_different, r_of_w_same]

theorem listGateStage_bounded_compare (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 1248#64) :
    p1248.effect s = listGateStage s (base + 1252#64)
      (AddWithCarry ((r (.GPR 8#5) s).setWidth 32) (~~~3#32) 1#1).2 := by
  change r .PC s = _ at pc
  rw [list_gate_compare_effect, pc]
  have nextPC : base + 1248#64 + 4#64 = base + 1252#64 := by bv_omega
  rw [nextPC]
  simp only [listGateStage]

theorem listGateStage_progressive_compare (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 684#64) :
    p684.effect s = listGateStage s (base + 688#64)
      (AddWithCarry ((r (.GPR 8#5) s).setWidth 32) (~~~3#32) 1#1).2 := by
  have compare : p684.effect s = p1248.effect s := rfl
  change r .PC s = _ at pc
  rw [compare, list_gate_compare_effect, pc]
  have nextPC : base + 684#64 + 4#64 = base + 688#64 := by bv_omega
  rw [nextPC]
  simp only [listGateStage]

private theorem list_gate_bounded_branch_effect (s : ArmState) :
    p1252.effect s = w .PC
      (if r (.FLAG .Z) s = 1#1 then r .PC s + 4#64 else r .PC s + 2672#64) s := by
  change exec_inst (.BR (.Cond_branch_imm { imm19 := 668, o0 := 0, cond := 1 })) s = _
  by_cases zero : r (.FLAG .Z) s = 1#1 <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, zero]

private theorem list_gate_progressive_branch_effect (s : ArmState) :
    p688.effect s = w .PC
      (if r (.FLAG .Z) s = 1#1 then r .PC s + 4#64 else r .PC s + 3236#64) s := by
  change exec_inst (.BR (.Cond_branch_imm { imm19 := 809, o0 := 0, cond := 1 })) s = _
  by_cases zero : r (.FLAG .Z) s = 1#1 <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, zero]

theorem listGateStage_bounded_branch (s : ArmState) (base : BitVec 64) (flags : PState) :
    p1252.effect (listGateStage s (base + 1252#64) flags) =
      w .PC (if flags.z = 1#1 then base + 1256#64 else base + 3924#64) (write_pstate flags s) := by
  rw [list_gate_bounded_branch_effect, listGateStage_zero, listGateStage_pc]
  have nextPC : base + 1252#64 + 4#64 = base + 1256#64 := by bv_omega
  have targetPC : base + 1252#64 + 2672#64 = base + 3924#64 := by bv_omega
  rw [nextPC, targetPC]
  unfold listGateStage
  exact w_of_w_shadow

theorem listGateStage_progressive_branch (s : ArmState) (base : BitVec 64) (flags : PState) :
    p688.effect (listGateStage s (base + 688#64) flags) =
      w .PC (if flags.z = 1#1 then base + 692#64 else base + 3924#64) (write_pstate flags s) := by
  rw [list_gate_progressive_branch_effect, listGateStage_zero, listGateStage_pc]
  have nextPC : base + 688#64 + 4#64 = base + 692#64 := by bv_omega
  have targetPC : base + 688#64 + 3236#64 = base + 3924#64 := by bv_omega
  rw [nextPC, targetPC]
  unfold listGateStage
  exact w_of_w_shadow

theorem list_gate_two_steps (s a b : ArmState) (first : stepi s = a)
    (second : stepi a = b) : run 2 s = b := by
  change stepi (stepi s) = b
  exact (congrArg stepi first).trans second

end SszArm.Measure.Bits.ListEntry

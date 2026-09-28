import SszArm.MeasureBitVectorOps

namespace SszArm.Measure.BitVector

open Result

macro "measure_bitvector_branch_fields" : tactic => `(tactic|
  (apply state_eq_iff_components_eq.mpr
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
       [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]))

theorem gate_compare_effect (s : ArmState) :
    p568.effect s = w .PC (r .PC s + 4#64)
      (write_pstate (AddWithCarry ((r (.GPR 8#5) s).setWidth 32) (~~~3#32) 1#1).2 s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 0, op := 1, S := 1, sh := 0, imm12 := 3, Rn := 8, Rd := 31 })) s = _
  measure_bitvector_branch_fields

theorem gate_branch_effect (s : ArmState) :
    p572.effect s = w .PC
      (if r (.FLAG .Z) s = 1#1 then r .PC s + 4#64 else r .PC s + 3352#64) s := by
  change exec_inst (.BR (.Cond_branch_imm { imm19 := 838, o0 := 0, cond := 1 })) s = _
  by_cases zero : r (.FLAG .Z) s = 1#1 <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, zero]

theorem scan_count_effect (s : ArmState) :
    p592.effect s = w .PC (r .PC s + 4#64)
      (write_pstate (AddWithCarry (r (.GPR 13#5) s) 1#64 0#1).2 s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 1, op := 0, S := 1, sh := 0, imm12 := 1, Rn := 13, Rd := 31 })) s = _
  measure_bitvector_branch_fields

theorem scan_zero_branch_effect (s : ArmState) :
    p596.effect s = w .PC
      (if r (.FLAG .Z) s = 1#1 then r .PC s + 2232#64 else r .PC s + 4#64) s := by
  change exec_inst (.BR (.Cond_branch_imm { imm19 := 558, o0 := 0, cond := 0 })) s = _
  by_cases zero : r (.FLAG .Z) s = 1#1 <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, zero]

end SszArm.Measure.BitVector

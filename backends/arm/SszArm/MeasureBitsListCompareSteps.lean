import SszArm.MeasureBitsListOps
import SszArm.MeasureHelpersNative
import SszArm.DelimitedIntegerFacts

namespace SszArm.Measure.Bits.ListEntry

open Result

theorem list_compare_extend_effect (s : ArmState) :
    p1732.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 8#5) ((((r (.GPR 0#5) s).setWidth 8).signExtend 32).setWidth 64) s) := by
  change exec_inst (.DPI (.Bitfield
    { sf := 0, opc := 0, N := 0, immr := 0, imms := 7, Rn := 0, Rd := 8 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
      Delimited.sxt_byte_mask, -BitVec.replicate_succ]
  all_goals exact w_of_w_commute (by decide)

theorem list_compare_flags_effect (s : ArmState) :
    p1736.effect s = w .PC (r .PC s + 4#64)
      (write_pstate (AddWithCarry ((r (.GPR 8#5) s).setWidth 32) (~~~1#32) 1#1).2 s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 0, op := 1, S := 1, sh := 0, imm12 := 1, Rn := 8, Rd := 31 })) s = _
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

theorem list_compare_branch_effect (s : ArmState) :
    p1740.effect s = w .PC
      (if r (.FLAG .N) s = r (.FLAG .V) s then r .PC s + 4#64 else r .PC s + 112#64) s := by
  change exec_inst (.BR (.Cond_branch_imm { imm19 := 28, o0 := 0, cond := 11 })) s = _
  by_cases nonnegative : r (.FLAG .N) s = r (.FLAG .V) s <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, nonnegative]

theorem list_compare_ordering_flags (order : Ordering) :
    let signed := (SszNative.NatABI.orderingByte order).signExtend 32
    let flags := (AddWithCarry signed (~~~1#32) 1#1).2
    (flags.n = flags.v) ↔ order = .gt := by
  cases order <;> decide

end SszArm.Measure.Bits.ListEntry

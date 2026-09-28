import SszArm.MeasureBitsListOptionSteps

namespace SszArm.Measure.Bits.ListEntry

open Result

def optionOps : Bool → Bool → List Op
  | false, false => [p716, p720, p724, p728, p732, p736, p740, p756]
  | false, true => [p716, p720, p724, p728, p744, p748, p752]
  | true, false => [p1584, p1588, p1592, p1596, p1612, p1616, p1620]
  | true, true => [p1584, p1588, p1592, p1596, p1600, p1604, p1608, p1624]

@[irreducible] def selected (hasCap : Bool) (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + if hasCap then 1712#64 else 1852#64) (NatCompare.saved s 9#5)

theorem option_run (large hasCap : Bool) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + if large then 1584#64 else 716#64)
    (option : (r (.GPR 8#5) s).setWidth 32 &&& 1#32 = if hasCap then 1#32 else 0#32)
    (stackLow : 16 ≤ (r (.GPR 31#5) s).toNat) :
    run (optionOps large hasCap).length s = selected hasCap s base := by
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have restored : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (NatCompare.saved s 9#5) =
      r (.GPR 9#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base (optionOps large hasCap) s := by
    cases large <;> cases hasCap <;>
      simp (config := {decide := true, instances := true})
        [Follows, optionOps, option716_effect, option720_effect, option724_effect,
          option728_effect, option732_effect, option736_effect, option740_effect,
          option744_effect, option748_effect, option752_effect, option756_effect,
          option1584_effect, option1588_effect, option1592_effect, option1596_effect,
          option1600_effect, option1604_effect, option1608_effect, option1612_effect,
          option1616_effect, option1620_effect, option1624_effect,
          CheckSPAlignment, state_simp_rules, bitvec_rules, lower, error, pc, option,
          NatExact.store_w, BitVec.add_assoc, BitVec.sub_add_cancel]
    all_goals simp [p716, p720, p724, p728, p732, p736, p740, p744, p748, p752,
      p756, p1584, p1588, p1592, p1596, p1600, p1604, p1608, p1612, p1616,
      p1620, p1624]
  rw [runs _ s base code follows]
  simp only [NatCompare.saved] at restored
  cases large <;> cases hasCap <;>
    simp (config := {decide := true, instances := true})
      [effect, optionOps, option716_effect, option720_effect, option724_effect,
        option728_effect, option732_effect, option736_effect, option740_effect,
        option744_effect, option748_effect, option752_effect, option756_effect,
        option1584_effect, option1588_effect, option1592_effect, option1596_effect,
        option1600_effect, option1604_effect, option1608_effect, option1612_effect,
        option1616_effect, option1620_effect, option1624_effect,
        CheckSPAlignment, state_simp_rules, bitvec_rules, lower, pc, option,
        NatExact.store_w, NatExact.gpr_w_pc, BitVec.add_assoc, BitVec.sub_add_cancel]
  all_goals
    apply state_eq_iff_components_eq.mpr
    refine ⟨?_, ?_, ?_⟩
    · intro field
      cases field with
      | GPR reg =>
        by_cases r9 : reg = 9#5
        · subst reg
          simp (config := {decide := true, instances := true})
            [selected, NatCompare.saved, state_simp_rules, restored]
        · by_cases rsp : reg = 31#5
          · subst reg
            simp (config := {decide := true, instances := true})
              [selected, NatCompare.saved, state_simp_rules, restored]
          · simp (config := {decide := true, instances := true})
              [selected, NatCompare.saved, state_simp_rules, r9, rsp, restored]
      | PC | SFP _ | FLAG _ | ERR =>
        simp [selected, NatCompare.saved, state_simp_rules]
    · simp [selected, NatCompare.saved, state_simp_rules]
    · intro n address
      simp [selected, NatCompare.saved, state_simp_rules]

end SszArm.Measure.Bits.ListEntry

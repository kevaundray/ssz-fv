import SszArm.MeasureScalarListSmallBranchSteps

namespace SszArm.Measure.Scalar.Bytes

open Result

def smallBranchOps (s : ArmState) : List Op :=
  [p2008, p2012, p2016, p2020] ++
    if (r (.GPR 11#5) s).setWidth 32 &&& 1#32 = 0#32 then [p2024, p2028, p2032]
    else [p2036, p2040, p2044]

@[irreducible] def smallBranchResult (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + if (r (.GPR 11#5) s).setWidth 32 &&& 1#32 = 0#32 then 2048#64 else 2388#64)
    (NatCompare.saved s 9#5)

macro "measure_small_branch_reduce" : tactic => `(tactic|
  simp_all (config := {decide := true})
    [effect, smallBranchResult, NatCompare.saved,
     SmallBranchSteps.p2008_effect, SmallBranchSteps.p2012_effect, SmallBranchSteps.p2016_effect, SmallBranchSteps.p2020_effect, SmallBranchSteps.p2024_effect, SmallBranchSteps.p2028_effect, SmallBranchSteps.p2032_effect, SmallBranchSteps.p2036_effect, SmallBranchSteps.p2040_effect, SmallBranchSteps.p2044_effect,
     state_simp_rules, BitVec.add_assoc, BitVec.sub_add_cancel,
     NatCompare.read_spill_w, NatExact.store_w])

private theorem small_branch_effect (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 2008#64)
    (stackLow : 16 ≤ (r (.GPR 31#5) s).toNat) :
    effect (smallBranchOps s) s = smallBranchResult s base := by
  have restore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (NatCompare.saved s 9#5) = r (.GPR 9#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  change r .PC s = _ at pc
  simp only [NatCompare.saved] at restore
  by_cases same : (r (.GPR 11#5) s).setWidth 32 &&& 1#32 = 0#32 <;>
    simp only [smallBranchOps, same, ↓reduceIte]
  all_goals apply state_eq_iff_components_eq.mpr
  all_goals
    refine ⟨?_, ?_, ?_⟩
    · intro field
      cases field with
      | GPR reg =>
        by_cases nine : reg = 9#5
        · subst reg
          measure_small_branch_reduce
        · by_cases sp : reg = 31#5
          · subst reg
            measure_small_branch_reduce
          · measure_small_branch_reduce
      | PC => measure_small_branch_reduce
      | SFP reg => measure_small_branch_reduce
      | FLAG flag => measure_small_branch_reduce
      | ERR => measure_small_branch_reduce
    · measure_small_branch_reduce
    · intro bytes address
      measure_small_branch_reduce


theorem small_branch_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 2008#64)
    (stackLow : 16 ≤ (r (.GPR 31#5) s).toNat) : run 7 s = smallBranchResult s base := by
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  have follows : Follows base (smallBranchOps s) s := by
    change r .PC s = _ at pc
    change r .ERR s = _ at error
    by_cases same : (r (.GPR 11#5) s).setWidth 32 &&& 1#32 = 0#32 <;>
      simp only [smallBranchOps, same, ↓reduceIte]
    all_goals simp_all (config := {decide := true})
      [Follows, SmallBranchSteps.p2008_effect, SmallBranchSteps.p2012_effect, SmallBranchSteps.p2016_effect, SmallBranchSteps.p2020_effect, SmallBranchSteps.p2024_effect, SmallBranchSteps.p2028_effect, SmallBranchSteps.p2036_effect, SmallBranchSteps.p2040_effect,
       show p2008.offset = 2008 from rfl,
       show p2012.offset = 2012 from rfl,
       show p2016.offset = 2016 from rfl,
       show p2020.offset = 2020 from rfl,
       show p2024.offset = 2024 from rfl,
       show p2028.offset = 2028 from rfl,
       show p2032.offset = 2032 from rfl,
       show p2036.offset = 2036 from rfl,
       show p2040.offset = 2040 from rfl,
       show p2044.offset = 2044 from rfl,
       state_simp_rules, BitVec.add_assoc]
  rw [show 7 = (smallBranchOps s).length by
    unfold smallBranchOps; split <;> rfl, runs _ s base code follows]
  exact small_branch_effect s base aligned pc stackLow


theorem small_branch_frame (s : ArmState) (base : BitVec 64)
    (stackLow : 16 ≤ (r (.GPR 31#5) s).toNat) :
    NatNarrow.Frame s (smallBranchResult s base) := by
  have frame := NatNarrow.saved_frame s 9#5 stackLow
  constructor
  · simpa [smallBranchResult, state_simp_rules] using frame.program
  · simpa [smallBranchResult, state_simp_rules] using frame.error
  · intro reg outside; simpa [smallBranchResult, state_simp_rules] using frame.registers reg outside
  · intro reg; simpa [smallBranchResult, state_simp_rules] using frame.vectors reg
  · intro address outside; simpa [smallBranchResult, state_simp_rules] using frame.memory address outside

end SszArm.Measure.Scalar.Bytes

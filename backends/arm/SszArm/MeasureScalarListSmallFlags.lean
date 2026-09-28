import SszArm.MeasureScalarListSmallFlagSteps

namespace SszArm.Measure.Scalar.Bytes

open Result

def smallFlagOps (actual cap : BitVec 64) : List Op :=
  [p1960, p1964] ++ (if actual = 0#64 then [p1968, p1972] else [p1976]) ++
  [p1980, p1984] ++ (if cap = 0#64 then [p1988, p1992] else [p1996]) ++ [p2000, p2004]

@[irreducible] def smallFlagsResult (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 2008#64)
    (w (.GPR 11#5) (if (r (.GPR 20#5) s = 0#64 ↔ r (.GPR 9#5) s = 0#64) then 0#64 else 1#64)
      (w (.GPR 10#5) (if r (.GPR 9#5) s = 0#64 ∧ r (.GPR 20#5) s ≠ 0#64 then 1#64 else 0#64)
        (write_pstate (AddWithCarry (r (.GPR 9#5) s) (~~~0#64) 1#1).2 s)))

macro "measure_small_flags_reduce" : tactic => `(tactic|
  simp_all (config := {decide := true})
    [effect, SmallFlagSteps.p1960_effect, SmallFlagSteps.p1964_effect,
     SmallFlagSteps.p1968_effect, SmallFlagSteps.p1972_effect,
     SmallFlagSteps.p1976_effect, SmallFlagSteps.p1980_effect,
     SmallFlagSteps.p1984_effect, SmallFlagSteps.p1988_effect,
     SmallFlagSteps.p1992_effect, SmallFlagSteps.p1996_effect,
     SmallFlagSteps.p2000_effect, SmallFlagSteps.p2004_effect,
     state_simp_rules, BitVec.add_assoc])

private theorem small_flags_effect (s : ArmState) (base : BitVec 64)
    (actualFlags capFlags : PState)
    (actualComparison : (AddWithCarry (r (.GPR 20#5) s) (~~~0#64) 1#1).2 = actualFlags)
    (capComparison : (AddWithCarry (r (.GPR 9#5) s) (~~~0#64) 1#1).2 = capFlags)
    (actualZero : actualFlags.z = 1#1 ↔ r (.GPR 20#5) s = 0#64)
    (capZero : capFlags.z = 1#1 ↔ r (.GPR 9#5) s = 0#64)
    (pc : read_pc s = base + 1960#64) :
    effect (smallFlagOps (r (.GPR 20#5) s) (r (.GPR 9#5) s)) s =
      w .PC (base + 2008#64)
        (w (.GPR 11#5) (if (r (.GPR 20#5) s = 0#64 ↔ r (.GPR 9#5) s = 0#64) then 0#64 else 1#64)
          (w (.GPR 10#5) (if r (.GPR 9#5) s = 0#64 ∧ r (.GPR 20#5) s ≠ 0#64 then 1#64 else 0#64)
            (write_pstate capFlags s))) := by
  change r .PC s = _ at pc
  by_cases actualEmpty : r (.GPR 20#5) s = 0#64 <;>
    by_cases capEmpty : r (.GPR 9#5) s = 0#64 <;>
    simp only [smallFlagOps, actualEmpty, capEmpty, ↓reduceIte]
  all_goals apply state_eq_iff_components_eq.mpr
  all_goals
    refine ⟨?_, ?_, ?_⟩
    · intro field
      cases field with
      | GPR reg =>
        by_cases ten : reg = 10#5
        · subst reg
          measure_small_flags_reduce
        · by_cases eleven : reg = 11#5
          · subst reg
            measure_small_flags_reduce
          · measure_small_flags_reduce
      | PC => measure_small_flags_reduce
      | SFP reg => measure_small_flags_reduce
      | FLAG flag => cases flag <;> measure_small_flags_reduce
      | ERR => measure_small_flags_reduce
    · measure_small_flags_reduce
    · intro bytes address
      measure_small_flags_reduce


theorem small_flags_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 1960#64) :
    run (smallFlagOps (r (.GPR 20#5) s) (r (.GPR 9#5) s)).length s = smallFlagsResult s base := by
  have actualZero := Udivti3.cmp_zero (r (.GPR 20#5) s) 0#64
  have capZero := Udivti3.cmp_zero (r (.GPR 9#5) s) 0#64
  let ops := smallFlagOps (r (.GPR 20#5) s) (r (.GPR 9#5) s)
  have follows : Follows base ops s := by
    change r .PC s = _ at pc
    change r .ERR s = _ at error
    by_cases actualEmpty : r (.GPR 20#5) s = 0#64 <;>
      by_cases capEmpty : r (.GPR 9#5) s = 0#64 <;>
      simp only [ops, smallFlagOps, actualEmpty, capEmpty, ↓reduceIte]
    all_goals simp_all (config := {decide := true})
      [Follows, SmallFlagSteps.p1960_effect, SmallFlagSteps.p1964_effect, SmallFlagSteps.p1968_effect, SmallFlagSteps.p1972_effect, SmallFlagSteps.p1976_effect, SmallFlagSteps.p1980_effect, SmallFlagSteps.p1984_effect, SmallFlagSteps.p1988_effect, SmallFlagSteps.p1992_effect, SmallFlagSteps.p1996_effect, SmallFlagSteps.p2000_effect,
       show p1960.offset = 1960 from rfl,
       show p1964.offset = 1964 from rfl,
       show p1968.offset = 1968 from rfl,
       show p1972.offset = 1972 from rfl,
       show p1976.offset = 1976 from rfl,
       show p1980.offset = 1980 from rfl,
       show p1984.offset = 1984 from rfl,
       show p1988.offset = 1988 from rfl,
       show p1992.offset = 1992 from rfl,
       show p1996.offset = 1996 from rfl,
       show p2000.offset = 2000 from rfl,
       show p2004.offset = 2004 from rfl,
       state_simp_rules, BitVec.add_assoc]
  rw [runs ops s base code follows]
  simpa only [smallFlagsResult] using small_flags_effect s base _ _ rfl rfl actualZero capZero pc


theorem small_flags_frame (s : ArmState) (base : BitVec 64) :
    NatNarrow.Frame s (smallFlagsResult s base) := by
  constructor
  · simp [smallFlagsResult, state_simp_rules]
  · simp [smallFlagsResult, state_simp_rules]
  · intro reg outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    simp (disch := simp_all) [smallFlagsResult, state_simp_rules]
  · intro reg; simp [smallFlagsResult, state_simp_rules]
  · intro address outside; simp [smallFlagsResult, state_simp_rules]

end SszArm.Measure.Scalar.Bytes

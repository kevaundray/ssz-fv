import SszArm.MeasureBitVectorCompareHeadStages

namespace SszArm.Measure.BitVector

open Result

@[irreducible] def compareHead (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (if r (.GPR 11#5) s = r (.GPR 9#5) s then base + 3296#64 else base + 3284#64)
    (w (.GPR 31#5) (r (.GPR 31#5) s - 16#64)
      (write_pstate (AddWithCarry (r (.GPR 11#5) s) (~~~r (.GPR 9#5) s) 1#1).2
        (NatCompare.saved s 9#5)))

@[irreducible] def compareChoice (equalHigh : Bool) (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 3300#64)
    (if equalHigh then
      write_pstate (AddWithCarry (r (.GPR 10#5) s) (~~~r (.GPR 8#5) s) 1#1).2 s
    else
      write_pstate (AddWithCarry 1#32 0#32 0#1).2 (w (.GPR 9#5) 1#64 s))

@[irreducible] def compareTail (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (if r (.FLAG .Z) s = 0#1 then base + 3320#64 else base + 3312#64)
    (w (.GPR 31#5) (r (.GPR 31#5) s + 16#64)
      (w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 31#5) s) s) s))

theorem compareHead_aligned (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (compareHead s base) := by
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  simpa [compareHead, NatCompare.saved, CheckSPAlignment, state_simp_rules] using lower

theorem compareChoice_aligned (equalHigh : Bool) (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (compareChoice equalHigh s base) := by
  cases equalHigh <;>
    simpa (config := {decide := true})
      [compareChoice, CheckSPAlignment, state_simp_rules] using aligned

private theorem compareHead_follows (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3268#64) : Follows base [p3268, p3272, p3276, p3280] s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  simp only [Follows, show p3268.offset = 3268 from rfl,
    show p3272.offset = 3272 from rfl, show p3276.offset = 3276 from rfl,
    show p3280.offset = 3280 from rfl]
  simp (config := {decide := true, instances := true})
    [compare3268_effect, compare3272_effect, compare3276_effect,
      CheckSPAlignment, state_simp_rules, lower, pc, error, BitVec.add_assoc]

private theorem compareHead_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3268#64) :
    effect [p3268, p3272, p3276, p3280] s = compareHead s base := by
  change effect [p3272, p3276, p3280] (p3268.effect s) = _
  rw [compareHeadMarked_compare s base pc, compareHeadMarked_remainder s base _ aligned]
  unfold compareHead
  simp only [Udivti3.cmp_zero]

theorem compareHead_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3268#64) : run 4 s = compareHead s base := by
  rw [show 4 = [p3268, p3272, p3276, p3280].length from rfl,
    runs _ s base code (compareHead_follows s base error aligned pc)]
  exact compareHead_summary s base aligned pc

private theorem compareChoice_follows (equalHigh : Bool) (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None)
    (pc : read_pc s = if equalHigh then base + 3296#64 else base + 3284#64) :
    Follows base (if equalHigh then [p3296] else [p3284, p3288, p3292]) s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  cases equalHigh <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Follows,
      show p3296.offset = 3296 from rfl, show p3284.offset = 3284 from rfl,
      show p3288.offset = 3288 from rfl, show p3292.offset = 3292 from rfl] at * <;>
    simp (config := {decide := true, instances := true})
      [compare3284_effect, compare3288_effect, state_simp_rules, pc, error, BitVec.add_assoc]

private theorem compareChoice_summary (equalHigh : Bool) (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = if equalHigh then base + 3296#64 else base + 3284#64) :
    effect (if equalHigh then [p3296] else [p3284, p3288, p3292]) s =
      compareChoice equalHigh s base := by
  change r .PC s = _ at pc
  cases equalHigh <;>
    simp (config := {decide := true, instances := true})
      [effect, compareChoice, compare3284_effect, compare3288_effect,
        compare3292_effect, compare3296_effect, state_simp_rules, pc, BitVec.add_assoc]
  all_goals simp only [w, write_base_pc, write_base_gpr, write_base_flag]

theorem compareChoice_run (equalHigh : Bool) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = if equalHigh then base + 3296#64 else base + 3284#64) :
    run (if equalHigh then 1 else 3) s = compareChoice equalHigh s base := by
  have count : (if equalHigh then 1 else 3) =
      (if equalHigh then [p3296] else [p3284, p3288, p3292]).length := by
    cases equalHigh <;> rfl
  rw [count, runs _ s base code (compareChoice_follows equalHigh s base error pc)]
  exact compareChoice_summary equalHigh s base pc

private theorem compareTail_follows (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3300#64) : Follows base [p3300, p3304, p3308] s := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  simp only [Follows, show p3300.offset = 3300 from rfl,
    show p3304.offset = 3304 from rfl, show p3308.offset = 3308 from rfl]
  simp (config := {decide := true, instances := true})
    [compare3300_effect, compare3304_effect, aligned, state_simp_rules, pc, error, BitVec.add_assoc]

private theorem compareTail_summary (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 3300#64) :
    effect [p3300, p3304, p3308] s = compareTail s base := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, compareTail, compare3300_effect, compare3304_effect, compare3308_effect,
      aligned, state_simp_rules, pc, BitVec.add_assoc, NatExact.gpr_w_pc] <;>
    simp only [w, write_base_pc, write_base_gpr]

theorem compareTail_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3300#64) : run 3 s = compareTail s base := by
  rw [show 3 = [p3300, p3304, p3308].length from rfl,
    runs _ s base code (compareTail_follows s base error aligned pc)]
  exact compareTail_summary s base aligned pc

end SszArm.Measure.BitVector

import SszArm.MeasureBitVectorComparePhases

namespace SszArm.Measure.BitVector

open Result

def compareOps (equalHigh : Bool) : List Op :=
  [p3268, p3272, p3276, p3280] ++
    (if equalHigh then [p3296] else [p3284, p3288, p3292]) ++ [p3300, p3304, p3308]

@[irreducible] def compared (s : ArmState) (base : BitVec 64) : ArmState :=
  let flags := if r (.GPR 11#5) s = r (.GPR 9#5) s then
      (AddWithCarry (r (.GPR 10#5) s) (~~~r (.GPR 8#5) s) 1#1).2
    else (AddWithCarry 1#32 0#32 0#1).2
  w .PC (if flags.z = 0#1 then base + 3320#64 else base + 3312#64)
    (write_pstate flags (NatCompare.saved s 9#5))

macro "measure_bitvector_compare_assemble_fields" : tactic => `(tactic|
  simp_all (config := {decide := true, instances := true})
    [compareHead, compareChoice, compareTail, compared, NatCompare.saved,
      state_simp_rules, NatExact.r_gpr_w, BitVec.sub_add_cancel])

private theorem compare_assemble (s : ArmState) (base : BitVec 64)
    (stackLow : 16 ≤ (r (.GPR 31#5) s).toNat) :
    compareTail
      (compareChoice (decide (r (.GPR 11#5) s = r (.GPR 9#5) s)) (compareHead s base) base)
      base = compared s base := by
  have restored : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64)
      (NatCompare.saved s 9#5) = r (.GPR 9#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  simp only [NatCompare.saved] at restored
  by_cases high : r (.GPR 11#5) s = r (.GPR 9#5) s
  all_goals
    apply state_eq_iff_components_eq.mpr
    refine ⟨?_, ?_, ?_⟩
    · intro field
      cases field with
      | GPR reg =>
        by_cases nine : reg = 9#5 <;> by_cases sp : reg = 31#5 <;>
          (try subst reg) <;> measure_bitvector_compare_assemble_fields
      | PC => measure_bitvector_compare_assemble_fields
      | SFP reg => measure_bitvector_compare_assemble_fields
      | FLAG flag => cases flag <;> measure_bitvector_compare_assemble_fields
      | ERR => measure_bitvector_compare_assemble_fields
    · measure_bitvector_compare_assemble_fields
    · intro bytes address
      measure_bitvector_compare_assemble_fields

theorem compare_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3268#64) (stackLow : 16 ≤ (r (.GPR 31#5) s).toNat) :
    run (compareOps (decide (r (.GPR 11#5) s = r (.GPR 9#5) s))).length s = compared s base := by
  let equalHigh := decide (r (.GPR 11#5) s = r (.GPR 9#5) s)
  let a := compareHead s base
  let b := compareChoice equalHigh a base
  have ap : a.program = s.program := by
    simp [a, compareHead, NatCompare.saved, state_simp_rules]
  have ae : read_err a = .None := by
    simpa [a, compareHead, NatCompare.saved, state_simp_rules] using error
  have aa : CheckSPAlignment a := compareHead_aligned s base aligned
  have ac : read_pc a = if equalHigh then base + 3296#64 else base + 3284#64 := by
    simp [a, equalHigh, compareHead, state_simp_rules]
  have first : run 4 s = a := compareHead_run s base code error aligned pc
  have second : run (if equalHigh then 1 else 3) a = b :=
    compareChoice_run equalHigh a base (code.congr ap) ae ac
  have bp : b.program = a.program := by
    dsimp only [b]
    cases equalHigh <;> simp [compareChoice, state_simp_rules]
  have be : read_err b = .None := by
    dsimp only [b]
    cases equalHigh <;> simpa [compareChoice, state_simp_rules] using ae
  have ba : CheckSPAlignment b := compareChoice_aligned equalHigh a base aa
  have bc : read_pc b = base + 3300#64 := by
    simp [b, compareChoice, state_simp_rules]
  have third : run 3 b = compareTail b base :=
    compareTail_run b base (code.congr (bp.trans ap)) be ba bc
  have count : (compareOps equalHigh).length = 4 + (if equalHigh then 1 else 3) + 3 := by
    cases equalHigh <;> rfl
  rw [count, run_plus, run_plus, first, second, third]
  exact compare_assemble s base stackLow

theorem compared_frame (s : ArmState) (base : BitVec 64)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat) : ScanFrame s (compared s base) := by
  have frame := NatCompare.saved_frame s 9#5 stack
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [compared, state_simp_rules] using frame.program
  · simpa [compared, state_simp_rules] using frame.error
  · intro reg outside
    simp [compared, NatCompare.saved, state_simp_rules]
  · intro reg
    simpa [compared, state_simp_rules] using frame.vectors reg
  · intro address outside
    simpa [compared, state_simp_rules] using frame.memory address outside

@[simp] theorem compared_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (compared s base) = r (.GPR reg) s := by
  simp [compared, NatCompare.saved, state_simp_rules]

theorem compared_pc (s : ArmState) (base : BitVec 64) :
    read_pc (compared s base) = base + BitVec.ofNat 64
      (if r (.GPR 11#5) s = r (.GPR 9#5) s ∧ r (.GPR 10#5) s = r (.GPR 8#5) s
        then 3312 else 3320) := by
  have constant : (AddWithCarry 1#32 0#32 0#1).2.z = 0#1 := by decide
  by_cases high : r (.GPR 11#5) s = r (.GPR 9#5) s <;>
    by_cases low : r (.GPR 10#5) s = r (.GPR 8#5) s <;>
      simp [compared, high, low, state_simp_rules, constant]

theorem compared_pc_success_iff (s : ArmState) (base : BitVec 64) :
    read_pc (compared s base) = base + 3312#64 ↔
      r (.GPR 11#5) s = r (.GPR 9#5) s ∧ r (.GPR 10#5) s = r (.GPR 8#5) s := by
  rw [compared_pc]
  by_cases equal : r (.GPR 11#5) s = r (.GPR 9#5) s ∧ r (.GPR 10#5) s = r (.GPR 8#5) s
  · simp [equal]
  · simp only [equal, ↓reduceIte, iff_false]
    bv_omega

end SszArm.Measure.BitVector

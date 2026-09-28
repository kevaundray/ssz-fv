import SszArm.MeasureBitVectorCapSelectStages

namespace SszArm.Measure.BitVector

open Result

def selectOps (wide : Bool) : List Op := [p644, p648, p652] ++ if wide then [p656] else []

@[irreducible] def selected (s : ArmState) (base : BitVec 64) : ArmState :=
  let count := r (.GPR 12#5) s + 1#64
  w .PC (if 3 ≤ count.toNat then base + 3320#64 else base + 2832#64)
    (write_pstate (AddWithCarry count (~~~3#64) 1#1).2 (w (.GPR 12#5) count s))

theorem select_run (s : ArmState) (base : BitVec 64) (code : CodeAt s base)
    (error : read_err s = .None) (pc : read_pc s = base + 644#64) :
    run (selectOps (decide (3 ≤ (r (.GPR 12#5) s + 1#64).toNat))).length s = selected s base := by
  let flags := (AddWithCarry (r (.GPR 12#5) s + 1#64) (~~~3#64) 1#1).2
  have first : stepi s = selectAdded s base :=
    (Op.step p644 s base code error pc).trans (selectAdded_add s base pc)
  have second : stepi (selectAdded s base) = selectMarked s base flags :=
    (Op.step p648 _ base (code.congr (selectAdded_program s base))
      ((selectAdded_error s base).trans error) (selectAdded_pc s base)).trans
        (selectAdded_compare s base)
  have third : stepi (selectMarked s base flags) = selectBranched s base flags :=
    (Op.step p652 _ base (code.congr (selectMarked_program s base flags))
      ((selectMarked_error s base flags).trans error) (selectMarked_pc s base flags)).trans
        (selectMarked_branch s base flags)
  have firstThree : run 3 s = selectBranched s base flags :=
    select_three_steps s _ _ _ first second third
  have carry : flags.c = 1#1 ↔ 3 ≤ (r (.GPR 12#5) s + 1#64).toNat :=
    Udivti3.cmp_carry (r (.GPR 12#5) s + 1#64) 3#64
  by_cases wide : 3 ≤ (r (.GPR 12#5) s + 1#64).toNat
  · have taken := carry.mpr wide
    have branchPC : read_pc (selectBranched s base flags) = base + 656#64 := by
      simp only [read_pc, selectBranched_pc, taken, ↓reduceIte]
    have jump : stepi (selectBranched s base flags) = selectJumped s base flags :=
      (Op.step p656 _ base (code.congr (selectBranched_program s base flags))
        ((selectBranched_error s base flags).trans error) branchPC).trans
          (selectBranched_jump s base flags taken)
    have count : (selectOps (decide (3 ≤ (r (.GPR 12#5) s + 1#64).toNat))).length = 4 := by
      simp only [wide, decide_true]
      rfl
    rw [count, show 4 = 3 + 1 from rfl, run_plus, firstThree]
    change stepi (selectBranched s base flags) = selected s base
    rw [jump]
    simp only [selectJumped, selected, wide, ↓reduceIte]
    rfl
  · have notTaken : flags.c ≠ 1#1 := fun same => wide (carry.mp same)
    have count : (selectOps (decide (3 ≤ (r (.GPR 12#5) s + 1#64).toNat))).length = 3 := by
      simp only [wide, decide_false]
      rfl
    rw [count, firstThree]
    simp only [selectBranched, selected, notTaken, wide, ↓reduceIte]
    rfl

theorem selected_frame (s : ArmState) (base : BitVec 64) : CapFrame s (selected s base) := by
  constructor
  · simp [selected, state_simp_rules]
  · simp [selected, state_simp_rules]
  · intro reg outside
    have different : reg ≠ 12#5 := fun equal => outside (by simp [equal])
    simp [selected, state_simp_rules, different]
  · intro reg
    simp [selected, state_simp_rules]
  · intro address outside
    simp [selected, state_simp_rules]

theorem selected_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5) (other : reg ≠ 12#5) :
    r (.GPR reg) (selected s base) = r (.GPR reg) s := by
  simp [selected, state_simp_rules, other]

end SszArm.Measure.BitVector

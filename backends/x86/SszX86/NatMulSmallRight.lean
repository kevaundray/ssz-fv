import SszX86.NatMulDispatch

namespace SszX86.NatMul

private theorem low_byte_append (hi : BitVec 56) (lo : BitVec 8) :
    (hi ++ lo).setWidth 8 = lo := BitVec.setWidth_append_eq_right

structure SmallRightPost (s : MachineData) (base : Int64) (t : MachineState) : Prop where
  frame : ControlFrame s t.1
  pointer : t.1.regs.rsi = s.regs.rsi
  payload : t.1.regs.rdx = s.regs.rdx
  factor : t.1.regs.r8 = s.regs.r8
  pc : t.2 = if s.regs.r10.toBitVec = 1#64 ∨ s.regs.r8.toBitVec = 0#64
    then base + 206 else base + 181

theorem scanned_small_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) :
    Eventually (step e) (SmallRightPost s base) (s, base + 100) := by
  have target := hc.targets ("natMul_u181", 181) (by decide)
  have rightFlag : (s.regs.r8.toBitVec == 0#64) = decide (s.regs.r8.toBitVec = 0#64) := by
    by_cases zero : s.regs.r8.toBitVec = 0#64
    · simp only [zero, beq_self_eq_true, decide_true]
    · simp only [beq_eq_false_iff_ne.mpr zero, zero, decide_false]
  by_cases leftZero : s.regs.r10.toBitVec = 1#64 <;>
    by_cases rightZero : s.regs.r8.toBitVec = 0#64
  all_goals
    natmul_step 1 row 2 using hc
    natmul_step 1 row 3 using hc
    natmul_step 1 row 4 using hc
    constructor <;> natmul_step 1 row 5 using hc
    all_goals
      natmul_step 1 row 6 using hc
      constructor <;> natmul_step 1 row 7 using hc
      all_goals
        simp [StatusFlags.from_result, leftZero, rightZero, target,
          low_byte_append, rightFlag, Effects.All]
        try natmul_step 1 row 8 using hc
        apply Eventually.done
        refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, ?_⟩
        simp [leftZero, rightZero]

end SszX86.NatMul

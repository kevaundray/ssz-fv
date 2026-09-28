import SszX86.NatMulDispatch

namespace SszX86.NatMul

def smallLeftState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rax := s.regs.rdx, r12 := 1}, status := flags}

def emptyLeftState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rax := 0, r12 := 0}, status := flags}

theorem small_left_dispatch_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (zero : s.regs.rdx.toBitVec = 0#64 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 119))
    (large : s.regs.rdx.toBitVec ≠ 0#64 → s.regs.rcx.toBitVec ≠ 0#64 → ∀ flags,
      Eventually (step e) P (smallLeftState s flags, base + 129))
    (small : s.regs.rdx.toBitVec ≠ 0#64 → s.regs.rcx.toBitVec = 0#64 → ∀ flags,
      Eventually (step e) P (smallLeftState s flags, base + 82)) :
    Eventually (step e) P (s, base + 63) := by
  have zeroTarget := hc.targets ("natMul_u119", 119) (by decide)
  have largeTarget := hc.targets ("natMul_u129", 129) (by decide)
  natmul_step 0 row 21 using hc
  constructor <;> natmul_step 0 row 22 using hc
  all_goals
    by_cases hz : s.regs.rdx.toBitVec = 0#64
    · simpa [StatusFlags.from_result, hz, zeroTarget, Effects.All] using zero hz _
    · simp [StatusFlags.from_result, hz, Effects.All]
      natmul_step 0 row 23 using hc
      natmul_step 0 row 24 using hc
      natmul_step 0 row 25 using hc
      constructor <;> natmul_step 0 row 26 using hc
      all_goals
        by_cases hr : s.regs.rcx.toBitVec = 0#64
        · simpa [StatusFlags.from_result, hr, smallLeftState, Effects.All] using small hz hr _
        · simpa [StatusFlags.from_result, hr, largeTarget, smallLeftState, Effects.All] using large hz hr _

theorem empty_left_dispatch_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (small : s.regs.rcx.toBitVec = 0#64 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 206))
    (large : s.regs.rcx.toBitVec ≠ 0#64 → ∀ flags, Eventually (step e) P
      (emptyLeftState s flags, base + 129)) :
    Eventually (step e) P (s, base + 119) := by
  have target := hc.targets ("natMul_u206", 206) (by decide)
  natmul_step 1 row 9 using hc
  constructor <;> natmul_step 1 row 10 using hc
  all_goals
    by_cases hz : s.regs.rcx.toBitVec = 0#64
    · simpa [StatusFlags.from_result, hz, target, Effects.All] using small hz _
    · simp [StatusFlags.from_result, hz, Effects.All]
      natmul_step 1 row 11 using hc
      constructor <;> natmul_step 1 row 12 using hc
      all_goals constructor <;> simpa [emptyLeftState] using large hz _

theorem small_right_dispatch_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (zero : s.regs.r8.toBitVec = 0#64 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 206))
    (nonzero : s.regs.r8.toBitVec ≠ 0#64 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 181)) :
    Eventually (step e) P (s, base + 82) := by
  have target := hc.targets ("natMul_u181", 181) (by decide)
  natmul_step 0 row 27 using hc
  constructor <;> natmul_step 0 row 28 using hc
  all_goals
    by_cases hz : s.regs.r8.toBitVec = 0#64
    · simp [StatusFlags.from_result, hz, Effects.All]
      natmul_step 0 row 29 using hc
      simpa using zero hz _
    · simpa [StatusFlags.from_result, hz, target, Effects.All] using nonzero hz _

end SszX86.NatMul

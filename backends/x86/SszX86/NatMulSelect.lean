import SszX86.NatMulDispatch

namespace SszX86.NatMul

def lowRightState (s : MachineData) (limb : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with r8 := UInt64.ofBitVec limb}, status := flags}

theorem right_count_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64)
    (first : s.regs.r13.toBitVec = 1#64 →
      Mem.loadInt s.dmem s.regs.rcx.toBitVec 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (zero : s.regs.r12.toBitVec = 0#64 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 206))
    (many : s.regs.r12.toBitVec ≠ 0#64 → s.regs.r13.toBitVec ≠ 1#64 → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 243))
    (one : s.regs.r12.toBitVec ≠ 0#64 → s.regs.r13.toBitVec = 1#64 → ∀ flags,
      Eventually (step e) P (lowRightState s limb flags, base + 181)) :
    Eventually (step e) P (s, base + 167) := by
  have zeroTarget := hc.targets ("natMul_u206", 206) (by decide)
  have manyTarget := hc.targets ("natMul_u243", 243) (by decide)
  natmul_step 1 row 24 using hc
  constructor <;> natmul_step 1 row 25 using hc
  all_goals
    by_cases hz : s.regs.r12.toBitVec = 0#64
    · simpa [StatusFlags.from_result, hz, zeroTarget, Effects.All] using zero hz _
    · simp [StatusFlags.from_result, hz, Effects.All]
      natmul_step 1 row 26 using hc
      natmul_step 1 row 27 using hc
      by_cases ho : s.regs.r13.toBitVec = 1#64
      · simp [StatusFlags.from_result, ho, Effects.All]
        natmul_step 1 row 28 using hc
        natmul_load (first ho)
        simpa [lowRightState] using one hz ho _
      · simpa [StatusFlags.from_result, ho, manyTarget, Effects.All] using many hz ho _

theorem count_select_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (one : s.regs.r12.toBitVec = 1#64 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 249))
    (many : s.regs.r12.toBitVec ≠ 1#64 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 275)) :
    Eventually (step e) P (s, base + 243) := by
  have target := hc.targets ("natMul_u275", 275) (by decide)
  natmul_step 2 row 18 using hc
  natmul_step 2 row 19 using hc
  by_cases ho : s.regs.r12.toBitVec = 1#64
  · simpa [StatusFlags.from_result, ho, Effects.All] using one ho _
  · simpa [StatusFlags.from_result, ho, target, Effects.All] using many ho _

theorem left_representation_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (small : s.regs.rsi.toBitVec = 0#64 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 709))
    (large : s.regs.rsi.toBitVec ≠ 0#64 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 258)) :
    Eventually (step e) P (s, base + 249) := by
  have target := hc.targets ("natMul_u709", 709) (by decide)
  natmul_step 2 row 20 using hc
  constructor <;> natmul_step 2 row 21 using hc
  all_goals
    by_cases hz : s.regs.rsi.toBitVec = 0#64
    · simpa [StatusFlags.from_result, hz, target, Effects.All] using small hz _
    · simpa [StatusFlags.from_result, hz, Effects.All] using large hz _

def lowLeftState (s : MachineData) (limb : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec limb}, status := flags}

theorem left_low_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64)
    (first : s.regs.rax.toBitVec ≠ 0#64 →
      Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (empty : s.regs.rax.toBitVec = 0#64 → ∀ flags, Eventually (step e) P
      (lowLeftState s 0 flags, base + 709))
    (nonempty : s.regs.rax.toBitVec ≠ 0#64 → ∀ flags, Eventually (step e) P
      (lowLeftState s limb flags, base + 709)) :
    Eventually (step e) P (s, base + 258) := by
  have target := hc.targets ("natMul_u707", 707) (by decide)
  natmul_step 2 row 22 using hc
  constructor <;> natmul_step 2 row 23 using hc
  all_goals
    by_cases hz : s.regs.rax.toBitVec = 0#64
    · simp [StatusFlags.from_result, hz, target, Effects.All]
      natmul_step 6 row 6 using hc
      constructor <;> simpa [lowLeftState] using empty hz _
    · simp [StatusFlags.from_result, hz, Effects.All]
      natmul_step 2 row 24 using hc
      natmul_load (first hz)
      natmul_step 2 row 25 using hc
      simpa [lowLeftState] using nonempty hz _

end SszX86.NatMul

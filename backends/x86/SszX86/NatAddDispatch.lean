import SszX86.NatAddCount

namespace SszX86.NatAdd

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The entry discriminator changes only flags, retaining both original pairs. -/
theorem entry_dispatch_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.rsi.toBitVec = 0#64 then base + 60 else base + 15)) :
    Eventually (step e) P (s, base + 10) := by
  have target := hc.targets ("natAdd_u60", 60) (by decide)
  natadd_step 6 using hc
  constructor <;> natadd_step 7 using hc
  all_goals
    by_cases zero : s.regs.rsi.toBitVec = 0#64
    · simpa [StatusFlags.from_result, zero, target, Effects.All] using next _
    · simpa [StatusFlags.from_result, zero, Effects.All] using next _

theorem left_count_entry_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with regs := {s.regs with rax := UInt64.ofBitVec (s.regs.rdx.toBitVec + 1#64)}}, base + 32)) :
    Eventually (step e) P (s, base + 15) := by
  natadd_step 8 using hc
  natadd_step 9 using hc
  natadd_step 10 using hc
  simpa only [BitVec.ofInt_add, BitVec.ofInt_toInt, show BitVec.ofInt 64 1 = 1#64 by decide] using next

theorem right_count_entry_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with regs := {s.regs with r10 := UInt64.ofBitVec (s.regs.r8.toBitVec + 1#64)}}, base + 160)) :
    Eventually (step e) P (s, base + 141) := by
  natadd_step 43 using hc
  natadd_step 44 using hc
  natadd_step 45 using hc
  simpa only [BitVec.ofInt_add, BitVec.ofInt_toInt, show BitVec.ofInt 64 1 = 1#64 by decide] using next

/-- All three predecessors test the actual right representation pointer. -/
theorem right_pointer_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (large : s.regs.rcx.toBitVec ≠ 0#64 → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 141))
    (small53 : s.regs.rcx.toBitVec = 0#64 → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 96))
    (small70 : s.regs.rcx.toBitVec = 0#64 → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 75)) :
    Eventually (step e) P (s, base + 53) ∧
      Eventually (step e) P (s, base + 70) ∧
      Eventually (step e) P (s, base + 91) := by
  have target := hc.targets ("natAdd_u141", 141) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · natadd_step 17 using hc
    constructor <;> natadd_step 18 using hc
    all_goals
      by_cases zero : s.regs.rcx.toBitVec = 0#64
      · simp [StatusFlags.from_result, zero, Effects.All]
        natadd_step 19 using hc
        exact small53 zero _
      · simpa [StatusFlags.from_result, zero, target, Effects.All] using large zero _
  · natadd_step 23 using hc
    constructor <;> natadd_step 24 using hc
    all_goals
      by_cases zero : s.regs.rcx.toBitVec = 0#64
      · simpa [StatusFlags.from_result, zero, Effects.All] using small70 zero _
      · simpa [StatusFlags.from_result, zero, target, Effects.All] using large zero _
  · natadd_step 29 using hc
    constructor <;> natadd_step 30 using hc
    all_goals
      by_cases zero : s.regs.rcx.toBitVec = 0#64
      · simpa [StatusFlags.from_result, zero, Effects.All] using small53 zero _
      · simpa [StatusFlags.from_result, zero, target, Effects.All] using large zero _

def rightMarked (s : MachineData) : MachineData :=
  {s with regs := {s.regs with
    r10 := UInt64.ofBitVec (s.regs.r10.toBitVec.extractLsb' 8 56 ++ 1#8)}}

/-- MOVB retains the high temporary bits; its low byte is the Large marker. -/
theorem right_nonzero_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({rightMarked s with status := flags},
        if s.regs.rax.toBitVec = 0#64 then base + 333 else base + 193)) :
    Eventually (step e) P (s, base + 181) := by
  have target := hc.targets ("natAdd_u333", 333) (by decide)
  natadd_step 52 using hc
  natadd_step 53 using hc
  constructor <;> natadd_step 54 using hc
  all_goals
    by_cases zero : s.regs.rax.toBitVec = 0#64
    · simpa [StatusFlags.from_result, zero, target, rightMarked, Effects.All] using next _
    · simpa [StatusFlags.from_result, zero, rightMarked, Effects.All] using next _

theorem right_zero_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags},
        if s.regs.rax.toBitVec = 0#64 then base + 333 else base + 271)) :
    Eventually (step e) P (s, base + 266) := by
  have target := hc.targets ("natAdd_u333", 333) (by decide)
  natadd_step 73 using hc
  constructor <;> natadd_step 74 using hc
  all_goals
    by_cases zero : s.regs.rax.toBitVec = 0#64
    · simpa [StatusFlags.from_result, zero, target, Effects.All] using next _
    · simpa [StatusFlags.from_result, zero, Effects.All] using next _

end SszX86.NatAdd

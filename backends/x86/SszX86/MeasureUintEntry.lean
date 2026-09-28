import SszX86.MeasureUintScan

namespace SszX86.Measure.Uint
open SszNative SszNative.Serialize UintCodec

/-- The real byte tag test includes wrong-type values, not just compatible inputs. -/
theorem tag_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags},
      if s.regs.rax.toBitVec.setWidth 8 = 1#8 then base + 803 else base + 3265)) :
    Eventually (step e) P (s, base + 795) := by
  have target := hc.targets ("measure_u3265", 3265) (by decide)
  measure_step 78 using hc
  measure_step 79 using hc
  by_cases compatible : s.regs.rax.toBitVec.setWidth 8 = 1#8
  · have zero : s.regs.rax.toBitVec.setWidth 8 - 1#8 = 0#8 := by rw [compatible]; decide
    simpa [compatible, zero, StatusFlags.from_result, Effects.All] using next _
  · have nonzero : s.regs.rax.toBitVec.setWidth 8 - 1#8 ≠ 0#8 := by
      intro zero
      apply compatible
      have same := congrArg (fun x : BitVec 8 => x + 1#8) zero
      simpa only [BitVec.sub_add_cancel, BitVec.zero_add] using same
    simpa [compatible, nonzero, target, StatusFlags.from_result, Effects.All] using next _

def numberHeader (s : MachineData) (pointer payload : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rdx := UInt64.ofBitVec pointer
      rcx := UInt64.ofBitVec payload}
    status := flags}

/-- Both Nat representation words are the original value fields. -/
theorem number_header_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer payload : BitVec 64)
    (hp : Mem.loadInt s.dmem (s.regs.r14.toBitVec + 8#64) 8 = some (pointer.toNat : Int))
    (hv : Mem.loadInt s.dmem (s.regs.r14.toBitVec + 16#64) 8 = some (payload.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (numberHeader s pointer payload flags,
      if pointer = 0#64 then base + 1720 else base + 820)) :
    Eventually (step e) P (s, base + 803) := by
  have target := hc.targets ("measure_u1720", 1720) (by decide)
  measure_step 80 using hc
  measure_uint_load hp
  measure_step 81 using hc
  measure_uint_load hv
  measure_step 82 using hc
  constructor <;> measure_step 83 using hc
  all_goals
    by_cases zero : pointer = 0#64
    · simpa [zero, target, numberHeader, StatusFlags.from_result, Effects.All] using next _
    · simpa [zero, numberHeader, StatusFlags.from_result, Effects.All] using next _

def numberLarge (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    rcx := UInt64.ofBitVec (s.regs.rcx.toBitVec + 1),
    rax := UInt64.ofBitVec (s.regs.rcx.toBitVec + 1), rdi := 0}, status := flags}

/-- INC count, clear required-low, initialize scan, and execute the real NOP. -/
theorem number_large_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (numberLarge s flags, base + 832)) :
    Eventually (step e) P (s, base + 820) := by
  measure_step 84 using hc
  measure_step 85 using hc
  constructor <;> measure_step 86 using hc
  all_goals
    measure_step 87 using hc
    simpa [numberLarge] using next _

def numberSmall (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rax := 7, rdx := 0}, status := flags}

/-- Small zero bypasses BSR; nonzero Small uses the same real lowering as Large. -/
theorem number_small_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (numberSmall s flags,
      if s.regs.rcx.toBitVec = 0#64 then base + 2684 else base + 1736)) :
    Eventually (step e) P (s, base + 1720) := by
  have target := hc.targets ("measure_u2684", 2684) (by decide)
  measure_step 231 using hc
  measure_step 232 using hc
  constructor <;> measure_step 233 using hc
  all_goals constructor <;> measure_step 234 using hc
  all_goals
    by_cases zero : s.regs.rcx.toBitVec = 0#64
    · simpa [zero, target, numberSmall, StatusFlags.from_result, Effects.All] using next _
    · simpa [zero, numberSmall, StatusFlags.from_result, Effects.All] using next _

theorem number_small_zero_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rdi := 0}, status := flags}, base + 2686)) :
    Eventually (step e) P (s, base + 2684) := by
  measure_step 345 using hc
  constructor <;> exact next _

theorem number_large_zero_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rdx := 0}, status := flags}, base + 2686)) :
    Eventually (step e) P (s, base + 2011) := by
  measure_step 286 using hc
  constructor <;> measure_step 287 using hc
  all_goals exact next _

end SszX86.Measure.Uint

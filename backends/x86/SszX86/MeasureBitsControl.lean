import SszX86.MeasureBitsEntry

namespace SszX86.Measure.Bits
open UintCodec

theorem vector_pointer_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.r8.toBitVec = 0#64
        then base + 1654 else base + 115)) :
    Eventually (step e) P (s, base + 106) := by
  have target := hc.targets ("measure_u1654", 1654) (by decide)
  measure_step 25 using hc
  constructor <;> measure_step 26 using hc
  all_goals
    by_cases zero : s.regs.r8.toBitVec = 0#64
    · simpa [zero, target, StatusFlags.from_result, Effects.All] using next _
    · simpa [zero, target, StatusFlags.from_result, Effects.All] using next _

theorem list_high_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.r14.toBitVec = 0#64
        then base + 912 else base + 1235)) :
    Eventually (step e) P (s, base + 903) := by
  have target := hc.targets ("measure_u1235", 1235) (by decide)
  measure_step 106 using hc
  constructor <;> measure_step 107 using hc
  all_goals
    by_cases zero : s.regs.r14.toBitVec = 0#64
    · simpa [zero, target, StatusFlags.from_result, Effects.All] using next _
    · simpa [zero, target, StatusFlags.from_result, Effects.All] using next _

theorem progressive_high_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.r14.toBitVec = 0#64
        then base + 966 else base + 1425)) :
    Eventually (step e) P (s, base + 957) := by
  have target := hc.targets ("measure_u1425", 1425) (by decide)
  measure_step 119 using hc
  constructor <;> measure_step 120 using hc
  all_goals
    by_cases zero : s.regs.r14.toBitVec = 0#64
    · simpa [zero, target, StatusFlags.from_result, Effects.All] using next _
    · simpa [zero, target, StatusFlags.from_result, Effects.All] using next _

theorem vector_mismatch_high_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.rdx.toBitVec = 0#64
        then base + 2810 else base + 2814)) :
    Eventually (step e) P (s, base + 2805) := by
  have target := hc.targets ("measure_u2814", 2814) (by decide)
  measure_step 381 using hc
  constructor <;> measure_step 382 using hc
  all_goals
    by_cases zero : s.regs.rdx.toBitVec = 0#64
    · simpa [zero, target, StatusFlags.from_result, Effects.All] using next _
    · simpa [zero, target, StatusFlags.from_result, Effects.All] using next _

theorem vector_empty_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.rdi.toBitVec = 0#64
        then base + 2780 else base + 1863)) :
    Eventually (step e) P (s, base + 1854) := by
  have target := hc.targets ("measure_u2780", 2780) (by decide)
  measure_step 257 using hc
  constructor <;> measure_step 258 using hc
  all_goals
    by_cases zero : s.regs.rdi.toBitVec = 0#64
    · simpa [zero, target, StatusFlags.from_result, Effects.All] using next _
    · simpa [zero, target, StatusFlags.from_result, Effects.All] using next _

end SszX86.Measure.Bits

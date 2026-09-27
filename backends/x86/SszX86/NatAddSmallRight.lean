import SszX86.NatAddCore

namespace SszX86.NatAdd

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem small_right_inline (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.r8.toBitVec = 0#64 then base + 326 else base + 661)) :
    Eventually (step e) P (s, base + 75) := by
  have target := hc.targets ("natAdd_u661", 661) (by decide)
  natadd_step 25 using hc
  constructor <;> natadd_step 26 using hc
  all_goals
    by_cases hz : s.regs.r8.toBitVec = 0#64
    · simp [StatusFlags.from_result, hz, Effects.All]
      natadd_step 27 using hc
      simpa only [hz, ↓reduceIte] using next _
    · simpa [StatusFlags.from_result, hz, target, Effects.All] using next _

theorem small_right_count (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with r11 := 1, r10 := 0}, status := flags}, base + 193)) :
    Eventually (step e) P (s, base + 117) := by
  natadd_step 36 using hc
  natadd_step 37 using hc
  constructor <;> natadd_step 38 using hc
  all_goals exact next _

theorem small_right_nonzero (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.r10.toBitVec = 1#64 then base + 585 else base + 117)) :
    Eventually (step e) P (s, base + 107) := by
  have target := hc.targets ("natAdd_u585", 585) (by decide)
  natadd_step 34 using hc
  natadd_step 35 using hc
  by_cases one : s.regs.r10.toBitVec = 1#64
  · simpa [StatusFlags.from_result, one, target, Effects.All] using next _
  · simpa [StatusFlags.from_result, one, Effects.All] using next _

theorem small_right_zero (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with r8 := 0}, status := flags},
        if s.regs.r10.toBitVec = 1#64 then base + 585 else base + 271)) :
    Eventually (step e) P (s, base + 569) := by
  have target := hc.targets ("natAdd_u271", 271) (by decide)
  natadd_step 147 using hc
  natadd_step 148 using hc
  natadd_step 149 using hc
  by_cases one : s.regs.r10.toBitVec = 1#64
  · simpa [StatusFlags.from_result, one, Effects.All] using next _
  · simpa [StatusFlags.from_result, one, target, Effects.All] using next _

theorem small_right_dispatch (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rcx := 0}, status := flags},
        if s.regs.r8.toBitVec = 0#64 then base + 569 else base + 107)) :
    Eventually (step e) P (s, base + 96) := by
  have target := hc.targets ("natAdd_u569", 569) (by decide)
  natadd_step 31 using hc
  constructor <;> natadd_step 32 using hc
  all_goals constructor <;> natadd_step 33 using hc
  all_goals
    by_cases hz : s.regs.r8.toBitVec = 0#64
    · simpa [StatusFlags.from_result, hz, target, Effects.All] using next _
    · simpa [StatusFlags.from_result, hz, Effects.All] using next _

end SszX86.NatAdd

import SszX86.NatAddCore
import SszX86.NatAddSmallSum

namespace SszX86.NatAdd

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem left_low_dispatch (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (small : s.regs.rsi.toBitVec = 0#64 → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 226))
    (empty : s.regs.rsi.toBitVec ≠ 0#64 → s.regs.rdx.toBitVec = 0#64 → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 623))
    (large : s.regs.rsi.toBitVec ≠ 0#64 → s.regs.rdx.toBitVec ≠ 0#64 → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 223)) :
    Eventually (step e) P (s, base + 209) := by
  have target226 := hc.targets ("natAdd_u226", 226) (by decide)
  have target623 := hc.targets ("natAdd_u623", 623) (by decide)
  natadd_step 59 using hc
  constructor <;> natadd_step 60 using hc
  all_goals
    by_cases hp : s.regs.rsi.toBitVec = 0#64
    · simpa [StatusFlags.from_result, hp, target226, Effects.All] using small hp _
    · simp [StatusFlags.from_result, hp, Effects.All]
      natadd_step 61 using hc
      constructor <;> natadd_step 62 using hc
      all_goals
        by_cases hz : s.regs.rdx.toBitVec = 0#64
        · simpa [StatusFlags.from_result, hz, target623, Effects.All] using empty hp hz _
        · simpa [StatusFlags.from_result, hz, Effects.All] using large hp hz _

theorem left_low_load (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64)
    (hm : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with regs := {s.regs with rdx := UInt64.ofBitVec limb}}, base + 226)) :
    Eventually (step e) P (s, base + 223) := by
  natadd_step 63 using hc
  natadd_load hm
  exact next

theorem right_low_select (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({sumStart s with status := flags},
        if s.regs.r10.toBitVec.setWidth 8 = 0#8 then base + 237 else base + 635)) :
    Eventually (step e) P (s, base + 226) := by
  have target := hc.targets ("natAdd_u635", 635) (by decide)
  natadd_step 64 using hc
  constructor <;> natadd_step 65 using hc
  all_goals constructor <;> natadd_step 66 using hc
  all_goals
    by_cases hz : s.regs.r10.toBitVec.setWidth 8 = 0#8
    · simpa [StatusFlags.from_result, hz, sumStart, Effects.All] using next _
    · simpa [StatusFlags.from_result, hz, target, sumStart, Effects.All] using next _

theorem left_empty_low (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rax := 0, rdx := 0}, status := flags},
        if s.regs.r10.toBitVec.setWidth 8 = 0#8 then base + 661 else base + 635)) :
    Eventually (step e) P (s, base + 623) := by
  have target := hc.targets ("natAdd_u661", 661) (by decide)
  natadd_step 165 using hc
  constructor <;> natadd_step 166 using hc
  all_goals natadd_step 167 using hc
  all_goals constructor <;> natadd_step 168 using hc
  all_goals
    by_cases hz : s.regs.r10.toBitVec.setWidth 8 = 0#8
    · simpa [StatusFlags.from_result, hz, target, Effects.All] using next _
    · simpa [StatusFlags.from_result, hz, Effects.All] using next _

theorem right_low_load (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (empty : s.regs.r8.toBitVec = 0#64 → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 841))
    (nonempty : s.regs.r8.toBitVec ≠ 0#64 → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 644)) :
    Eventually (step e) P (s, base + 635) := by
  have target := hc.targets ("natAdd_u841", 841) (by decide)
  natadd_step 169 using hc
  constructor <;> natadd_step 170 using hc
  all_goals
    by_cases hz : s.regs.r8.toBitVec = 0#64
    · simpa [StatusFlags.from_result, hz, target, Effects.All] using empty hz _
    · simpa [StatusFlags.from_result, hz, Effects.All] using nonempty hz _

theorem right_low_loaded (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64)
    (hm : Mem.loadInt s.dmem s.regs.rcx.toBitVec 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with regs := {s.regs with r8 := UInt64.ofBitVec limb}}, base + 647)) :
    Eventually (step e) P (s, base + 644) := by
  natadd_step 171 using hc
  natadd_load hm
  exact next

theorem inline_sum_entry (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P ({sumStart s with status := flags}, base + 663)) :
    Eventually (step e) P (s, base + 661) := by
  natadd_step 176 using hc
  constructor <;> simpa only [sumStart] using next _

theorem empty_sum_entry (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with r8 := 0}, status := flags}, base + 844)) :
    Eventually (step e) P (s, base + 841) := by
  natadd_step 214 using hc
  constructor <;> exact next _

end SszX86.NatAdd

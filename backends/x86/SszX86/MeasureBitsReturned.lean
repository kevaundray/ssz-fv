import SszX86.MeasureBitsCalls
import SszX86.NatFromU128Core

namespace SszX86.Measure.Bits
open UintCodec SszNative.NatABI

/-- NatCompare's signed Ordering byte is tested exactly as shipped. -/
theorem list_compared_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (ord : Ordering) (P : MachineState → Prop)
    (returned : s.regs.rax.toBitVec.setWidth 8 = orderingByte ord)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if ord = .gt then base + 1366 else base + 2079)) :
    Eventually (step e) P (s, base + 1358) := by
  have target := hc.targets ("measure_u2079", 2079) (by decide)
  measure_step 153 using hc
  constructor <;> measure_step 154 using hc
  all_goals cases ord <;>
    simpa [returned, orderingByte, show (255#8).msb = true by decide,
      target, StatusFlags.from_result, Effects.All] using next _

theorem progressive_compared_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (ord : Ordering) (P : MachineState → Prop)
    (returned : s.regs.rax.toBitVec.setWidth 8 = orderingByte ord)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if ord = .gt then base + 1562 else base + 1621)) :
    Eventually (step e) P (s, base + 1558) := by
  have target := hc.targets ("measure_u1621", 1621) (by decide)
  measure_step 197 using hc
  constructor <;> measure_step 198 using hc
  all_goals cases ord <;>
    simpa [returned, orderingByte, show (255#8).msb = true by decide,
      target, StatusFlags.from_result, Effects.All] using next _

/-- None bypasses only comparison, never the preceding count construction. -/
theorem progressive_option_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.rax.toBitVec.setWidth 8 &&& 1#8 = 0#8
        then base + 1621 else base + 1524)) :
    Eventually (step e) P (s, base + 1520) := by
  have target := hc.targets ("measure_u1621", 1621) (by decide)
  have selected : s.regs.rax.toBitVec.extractLsb' 0 8 = s.regs.rax.toBitVec.setWidth 8 := by
    rw [← BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]
  measure_step 187 using hc
  constructor <;> measure_step 188 using hc
  all_goals
    by_cases none : s.regs.rax.toBitVec.setWidth 8 &&& 1#8 = 0#8
    · simpa [selected, none, target, StatusFlags.from_result, Effects.All] using next _
    · simpa [selected, none, target, StatusFlags.from_result, Effects.All] using next _

def fromWideLoaded (s : MachineData) (reason : BitVec 32) (pointer payload : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rdx := UInt64.ofBitVec (reason.setWidth 64)
      rcx := UInt64.ofBitVec pointer
      rax := UInt64.ofBitVec payload}
    status := flags}

/-- Load the helper's actual result fields and dispatch without assuming success. -/
theorem from_wide_returned_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (reason : BitVec 32) (pointer payload : BitVec 64)
    (P : MachineState → Prop)
    (hs : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 88#64) 4 = some (reason.toNat : Int))
    (hp : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 24#64) 8 = some (pointer.toNat : Int))
    (hv : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 32#64) 8 = some (payload.toNat : Int))
    (next : ∀ flags, Eventually (step e) P
      (fromWideLoaded s reason pointer payload flags,
        if reason = 0#32 then base + 3052 else base + 2141)) :
    Eventually (step e) P (s, base + 2119) := by
  have target := hc.targets ("measure_u3052", 3052) (by decide)
  have selected (v : BitVec 64) : v.extractLsb' 0 32 = v.setWidth 32 := by
    rw [← BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]
  measure_step 297 using hc
  natfrom_load hs
  measure_step 298 using hc
  natfrom_load hp
  measure_step 299 using hc
  natfrom_load hv
  measure_step 300 using hc
  constructor <;> measure_step 301 using hc
  all_goals
    by_cases zero : reason = 0#32
    · simpa [selected, fromWideLoaded, zero, target, StatusFlags.from_result, Effects.All] using next _
    · simpa [selected, fromWideLoaded, zero, target, StatusFlags.from_result, Effects.All] using next _

end SszX86.Measure.Bits

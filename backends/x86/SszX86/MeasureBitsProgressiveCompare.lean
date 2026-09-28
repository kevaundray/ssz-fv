import SszX86.MeasureBitsSmall
import SszX86.MeasureBitsReturned

namespace SszX86.Measure.Bits
open UintCodec

def progressiveCompareMem (s : MachineData) : DataMem :=
  Mem.storeInt
    (Mem.storeInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 s.regs.rcx.toBitVec.toInt)
    (s.regs.rsp.toBitVec + 16#64) 8 s.regs.rsi.toBitVec.toInt

def progressiveCompareReady (s : MachineData) : MachineData :=
  {s with
    dmem := progressiveCompareMem s
    regs := {s.regs with rdi := s.regs.r13, rdx := s.regs.rbp, rcx := s.regs.r12}}

/-- The Some path saves the original arena header and the represented count
payload before NatCompare can clobber the argument registers. -/
theorem progressive_compare_prepare_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (work : Large.Mapped s.dmem s.regs.rsp.toBitVec 24)
    (next : Eventually (step e) P (progressiveCompareReady s, base + 1543)) :
    Eventually (step e) P (s, base + 1524) := by
  measure_step 189 using hc
  measure_step 190 using hc
  measure_step 191 using hc
  apply Delimited.store_cps
  · exact Large.mapped_load _ _ 24 8 8 work (by decide)
  simp only [Effects.All]
  measure_step 192 using hc
  measure_step 193 using hc
  apply Delimited.store_cps
  · apply Large.mapped_load (capacity := 24) («offset» := 16) («width» := 8)
    · exact Large.mapped_store _ _ _ _ _ _ work
    · decide
  simp only [Effects.All]
  simpa only [progressiveCompareReady, progressiveCompareMem] using next

theorem progressive_compare_reload_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (header payload : BitVec 64) (P : MachineState → Prop)
    (savedHeader : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 = some (header.toNat : Int))
    (savedPayload : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 16#64) 8 = some (payload.toNat : Int))
    (next : Eventually (step e) P
      ({s with regs := {s.regs with
        rdi := UInt64.ofBitVec payload
        rcx := UInt64.ofBitVec header}}, base + 1558)) :
    Eventually (step e) P (s, base + 1548) := by
  measure_step 195 using hc
  natfrom_load savedPayload
  measure_step 196 using hc
  natfrom_load savedHeader
  simpa using next

end SszX86.Measure.Bits

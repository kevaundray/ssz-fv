import SszX86.MeasureBitsProgressiveReserve
import SszX86.NatFromU128Commit

namespace SszX86.Measure.ProgressiveReservation
open UintCodec

def committed (s : MachineData) : MachineData :=
  {s with
    dmem := NatFromU128.commitMem s.dmem s.regs.rcx.toBitVec
      (s.regs.r9.toBitVec + s.regs.rsi.toBitVec) s.regs.rdi.toBitVec
      s.regs.r15.toBitVec s.regs.r14.toBitVec
    regs := {s.regs with
      r13 := UInt64.ofBitVec (s.regs.r9.toBitVec + s.regs.rsi.toBitVec)
      rsi := 2}}

/-- Progressive count allocation is independent of the option discriminant:
these three stores execute before the option is tested at1520. -/
theorem commit_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (header : ∃ old, Mem.loadInt s.dmem (s.regs.rcx.toBitVec + 16#64) 8 = some old)
    (payload : Large.Mapped s.dmem (s.regs.r9.toBitVec + s.regs.rsi.toBitVec) 16)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (committed s, base + 1520)) :
    Eventually (step e) P (s, base + 1498) := by
  measure_step 182 using hc
  apply Delimited.store_cps
  · exact header
  simp only [Effects.All]
  measure_step 183 using hc
  measure_step 184 using hc
  apply Delimited.store_cps
  · apply Delimited.mapped_load_zero (capacity := 16) (byteCount := 8)
    · exact Large.mapped_store _ _ _ _ _ _ payload
    · decide
  simp only [Effects.All]
  measure_step 185 using hc
  apply Delimited.store_cps
  · apply Large.mapped_load
      (dst := s.regs.r9.toBitVec + s.regs.rsi.toBitVec)
      (capacity := 16) («offset» := 8) («width» := 8)
    · exact Large.mapped_store _ _ _ _ _ _ (Large.mapped_store _ _ _ _ _ _ payload)
    · decide
  simp only [Effects.All]
  measure_step 186 using hc
  simpa [committed, NatFromU128.commitMem, BitVec.add_assoc] using next

end SszX86.Measure.ProgressiveReservation

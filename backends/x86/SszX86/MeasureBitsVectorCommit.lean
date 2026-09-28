import SszX86.MeasureBitsVectorReserve
import SszX86.NatFromU128Commit

namespace SszX86.Measure.VectorReservation
open UintCodec

def committed (s : MachineData) : MachineData :=
  {s with
    dmem := NatFromU128.commitMem s.dmem s.regs.rcx.toBitVec
      (s.regs.rdi.toBitVec + s.regs.r8.toBitVec) s.regs.r9.toBitVec
      s.regs.rax.toBitVec s.regs.rdx.toBitVec
    regs := {s.regs with
      rcx := UInt64.ofBitVec (s.regs.rdi.toBitVec + s.regs.r8.toBitVec)
      rax := 2}}

/-- The inlined vector count commits the header before either payload word.
The original low count survives until the first payload store. -/
theorem commit_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (header : ∃ old, Mem.loadInt s.dmem (s.regs.rcx.toBitVec + 16#64) 8 = some old)
    (payload : Large.Mapped s.dmem (s.regs.rdi.toBitVec + s.regs.r8.toBitVec) 16)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (committed s, base + 2893)) :
    Eventually (step e) P (s, base + 2871) := by
  measure_step 402 using hc
  apply Delimited.store_cps
  · exact header
  simp only [Effects.All]
  measure_step 403 using hc
  measure_step 404 using hc
  apply Delimited.store_cps
  · apply Delimited.mapped_load_zero (capacity := 16) (byteCount := 8)
    · exact Large.mapped_store _ _ _ _ _ _ payload
    · decide
  simp only [Effects.All]
  measure_step 405 using hc
  apply Delimited.store_cps
  · apply Large.mapped_load
      (dst := s.regs.rdi.toBitVec + s.regs.r8.toBitVec)
      (capacity := 16) («offset» := 8) («width» := 8)
    · exact Large.mapped_store _ _ _ _ _ _ (Large.mapped_store _ _ _ _ _ _ payload)
    · decide
  simp only [Effects.All]
  measure_step 406 using hc
  simpa [committed, NatFromU128.commitMem, BitVec.add_assoc] using next

end SszX86.Measure.VectorReservation

import SszX86.MeasureBitsListReserve
import SszX86.NatFromU128Commit

namespace SszX86.Measure.ListReservation
open UintCodec

def commitMem (s : MachineData) : DataMem :=
  let m := Mem.storeInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 s.regs.rcx.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rcx.toBitVec + 16#64) 8 s.regs.rsi.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rsp.toBitVec + 16#64) 8 s.regs.r15.toBitVec.toInt
  let pointer := s.regs.rax.toBitVec + s.regs.r8.toBitVec
  let m := Mem.storeInt m pointer 8 s.regs.r15.toBitVec.toInt
  Mem.storeInt m (pointer + 8#64) 8 s.regs.r14.toBitVec.toInt

def committed (s : MachineData) : MachineData :=
  {s with
    dmem := commitMem s
    regs := {s.regs with
      rbp := UInt64.ofBitVec (s.regs.rax.toBitVec + s.regs.r8.toBitVec)
      r15 := 2}}

/-- The exact five-write inline constructor: two spills, one cursor commit,
and two count words, in the shipped order. -/
theorem commit_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (header : Large.Mapped s.dmem s.regs.rcx.toBitVec 24)
    (work : Large.Mapped s.dmem s.regs.rsp.toBitVec 24)
    (payload : Large.Mapped s.dmem (s.regs.rax.toBitVec + s.regs.r8.toBitVec) 16)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (committed s, base + 1341)) :
    Eventually (step e) P (s, base + 1308) := by
  measure_step 141 using hc
  apply Delimited.store_cps
  · apply Large.mapped_load (capacity := 24) («offset» := 8) («width» := 8)
    · exact work
    · decide
  simp only [Effects.All]
  measure_step 142 using hc
  apply Delimited.store_cps
  · apply Large.mapped_load (capacity := 24) («offset» := 16) («width» := 8)
    · exact Large.mapped_store _ _ _ _ _ _ header
    · decide
  simp only [Effects.All]
  measure_step 143 using hc
  measure_step 144 using hc
  apply Delimited.store_cps
  · apply Large.mapped_load (capacity := 24) («offset» := 16) («width» := 8)
    · repeat' first | exact work | apply Large.mapped_store
    · decide
  simp only [Effects.All]
  measure_step 145 using hc
  apply Delimited.store_cps
  · apply Delimited.mapped_load_zero (capacity := 16) (byteCount := 8)
    · repeat' first | exact payload | apply Large.mapped_store
    · decide
  simp only [Effects.All]
  measure_step 146 using hc
  apply Delimited.store_cps
  · apply Large.mapped_load
      (dst := s.regs.rax.toBitVec + s.regs.r8.toBitVec)
      (capacity := 16) («offset» := 8) («width» := 8)
    · repeat' first | exact payload | apply Large.mapped_store
    · decide
  simp only [Effects.All]
  measure_step 147 using hc
  simpa [committed, commitMem, BitVec.add_assoc] using next

end SszX86.Measure.ListReservation

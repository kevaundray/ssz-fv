import SszX86.NatDivisionReserveSmallExec

namespace SszX86.NatDivision.Reservation.Small
open SszX86.NatDivision
open SszX86.Delimited

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def committedMem (s : MachineData) : DataMem :=
  let m := Mem.storeInt s.dmem (s.regs.r12.toBitVec + 16#64) 8 s.regs.rdi.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rcx.toBitVec + s.regs.rsi.toBitVec) 8 s.regs.rax.toBitVec.toInt
  Mem.storeInt m (s.regs.rcx.toBitVec + s.regs.rsi.toBitVec + 8#64) 8 s.regs.rdx.toBitVec.toInt

def committed (s : MachineData) : MachineData :=
  {s with
    dmem := committedMem s
    regs := {s.regs with
      rdi := UInt64.ofBitVec (s.regs.rcx.toBitVec + s.regs.rsi.toBitVec)
      rcx := 2}}

/-- The cursor is committed before the two exact limb stores and before the
remainder computation. Alignment padding is never written. -/
theorem commit_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (header : ∃ old, Mem.loadInt s.dmem (s.regs.r12.toBitVec + 16#64) 8 = some old)
    (payload : UintCodec.Large.Mapped s.dmem
      (s.regs.rcx.toBitVec + s.regs.rsi.toBitVec) 16)
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (committed s, base + 358)) :
    Eventually (step e) P (s, base + 335) := by
  natdiv_step 92 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply store_cps
  · exact header
  simp only [Effects.All]
  natdiv_step 93 using hc
  natdiv_step 94 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply store_cps
  · apply mapped_load_zero (capacity := 16) (byteCount := 8)
    · exact UintCodec.Large.mapped_store _ _ _ _ _ _ payload
    · decide
  simp only [Effects.All]
  natdiv_step 95 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply store_cps
  · apply UintCodec.Large.mapped_load
      (dst := s.regs.rcx.toBitVec + s.regs.rsi.toBitVec)
      (capacity := 16) (offset := 8) («width» := 8)
    · exact UintCodec.Large.mapped_store _ _ _ _ _ _
        (UintCodec.Large.mapped_store _ _ _ _ _ _ payload)
    · decide
  simp only [Effects.All]
  natdiv_step 96 using hc
  simpa [committed, committedMem, BitVec.add_assoc] using hp

end SszX86.NatDivision.Reservation.Small

import SszX86.NatAddReserveSmallExec

namespace SszX86.NatAdd.Reservation.Small
open SszX86.NatAdd
open SszX86.Delimited

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def committedMem (s : MachineData) : DataMem :=
  let m := Mem.storeInt s.dmem (s.regs.r9.toBitVec + 16#64) 8 s.regs.rsi.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rax.toBitVec + s.regs.rcx.toBitVec) 8 s.regs.rdx.toBitVec.toInt
  Mem.storeInt m (s.regs.rax.toBitVec + s.regs.rcx.toBitVec + 8#64) 8 1

def committed (s : MachineData) : MachineData :=
  {s with
    dmem := committedMem s
    regs := {s.regs with
      rsi := UInt64.ofBitVec (s.regs.rax.toBitVec + s.regs.rcx.toBitVec)}}

/-- The actual small-overflow block commits the cursor and writes exactly
`[low, 1]`, stopping before either output-pair store. -/
theorem commit_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (header : ∃ old, Mem.loadInt s.dmem (s.regs.r9.toBitVec + 16#64) 8 = some old)
    (payload : UintCodec.Large.Mapped s.dmem
      (s.regs.rax.toBitVec + s.regs.rcx.toBitVec) 16)
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (committed s, base + 750)) :
    Eventually (step e) P (s, base + 729) := by
  natadd_step 197 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply store_cps
  · exact header
  simp only [Effects.All]
  natadd_step 198 using hc
  natadd_step 199 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply store_cps
  · apply mapped_load_zero (capacity := 16) (byteCount := 8)
    · exact UintCodec.Large.mapped_store _ _ _ _ _ _ payload
    · decide
  simp only [Effects.All]
  natadd_step 200 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply store_cps
  · apply UintCodec.Large.mapped_load
      (dst := s.regs.rax.toBitVec + s.regs.rcx.toBitVec)
      (capacity := 16) (offset := 8) («width» := 8)
    · exact UintCodec.Large.mapped_store _ _ _ _ _ _
        (UintCodec.Large.mapped_store _ _ _ _ _ _ payload)
    · decide
  simp only [Effects.All]
  simpa [committed, committedMem, BitVec.add_assoc] using hp

end SszX86.NatAdd.Reservation.Small

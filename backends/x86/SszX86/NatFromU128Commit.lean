import SszX86.NatFromU128Reserve

namespace SszX86.NatFromU128
open UintCodec

def commitMem (m : DataMem) (arena pointer finish low high : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (arena + 16#64) 8 finish.toInt
  let m := Mem.storeInt m pointer 8 low.toInt
  Mem.storeInt m (pointer + 8#64) 8 high.toInt

def committed (s : MachineData) : MachineData :=
  {s with
    dmem := commitMem s.dmem s.regs.rcx.toBitVec
      (s.regs.r8.toBitVec + s.regs.r9.toBitVec) s.regs.r10.toBitVec
      s.regs.rsi.toBitVec s.regs.rdx.toBitVec
    regs := {s.regs with
      rcx := UInt64.ofBitVec (s.regs.r8.toBitVec + s.regs.r9.toBitVec)
      rsi := 2}}

/-- Commit only the cursor, then both full input words; alignment padding is not written. -/
theorem commit_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (header : ∃ old, Mem.loadInt s.dmem (s.regs.rcx.toBitVec + 16#64) 8 = some old)
    (payload : Large.Mapped s.dmem (s.regs.r8.toBitVec + s.regs.r9.toBitVec) 16)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (committed s, base + 95)) :
    Eventually (step e) P (s, base + 73) := by
  natfrom_step 25 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply Delimited.store_cps
  · exact header
  simp only [Effects.All]
  natfrom_step 26 using hc
  natfrom_step 27 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply Delimited.store_cps
  · apply Delimited.mapped_load_zero (capacity := 16) (byteCount := 8)
    · exact Large.mapped_store _ _ _ _ _ _ payload
    · decide
  simp only [Effects.All]
  natfrom_step 28 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply Delimited.store_cps
  · apply Large.mapped_load
      (dst := s.regs.r8.toBitVec + s.regs.r9.toBitVec)
      (capacity := 16) (offset := 8) («width» := 8)
    · exact Large.mapped_store _ _ _ _ _ _ (Large.mapped_store _ _ _ _ _ _ payload)
    · decide
  simp only [Effects.All]
  natfrom_step 29 using hc
  simpa [committed, commitMem, BitVec.add_assoc] using next

end SszX86.NatFromU128

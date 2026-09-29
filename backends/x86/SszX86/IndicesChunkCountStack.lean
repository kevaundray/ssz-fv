import SszX86.IndicesChunkCountExec

namespace SszX86.IndicesChunkCount
open UintCodec

def savedMem (s : MachineData) : DataMem :=
  let m := Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8) 8 s.regs.r14.toBitVec.toInt
  Mem.storeInt m (s.regs.rsp.toBitVec - 8 - 8) 8 s.regs.rbx.toBitVec.toInt

def entered (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 8 - 8 - 72)},
    dmem := savedMem s, status := flags}

/-- Only the two original PUSH slots are initialized on entry. The 72-byte
local result area remains arbitrary until its actual stores execute. -/
theorem entry_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData)
    (slot14 : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8)
    (slotBx : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 8 - 8) 8)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (entered s flags, base + 7)) :
    Eventually (step e) P (s, base) := by
  rw [← Int64.add_zero base]
  indices_count_step 0 using code
  apply Delimited.store_cps
  · exact Delimited.mapped_load_zero s.dmem _ 8 8 slot14 (by decide)
  simp only [Effects.All]
  indices_count_step 1 using code
  apply Delimited.store_cps
  · apply Delimited.mapped_load_zero (capacity := 8) (byteCount := 8)
    · exact Large.mapped_store _ _ _ _ _ _ slotBx
    · decide
  simp only [Effects.All]
  indices_count_step 2 using code
  have stack : s.regs.rsp - 8 - 8 =
      UInt64.ofBitVec (s.regs.rsp.toBitVec - 8 - 8) := by
    apply UInt64.toBitVec_inj.1
    simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat,
      UInt64.toBitVec_ofBitVec]
  simpa only [entered, savedMem, stack] using next _

def restored (s : MachineData) (rbx r14 : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 96),
    rbx := UInt64.ofBitVec rbx, r14 := UInt64.ofBitVec r14}, status := flags}

/-- All three original epilogues restore the two saved registers and pop the
original return address; success and error use exactly the same stack layout. -/
theorem epilogue_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (rbx r14 ra : BitVec 64)
    (savedBx : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 72#64) 8 =
      some (Int.ofBytes (wordBytes rbx)))
    (saved14 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 80#64) 8 =
      some (Int.ofBytes (wordBytes r14)))
    (ret : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 88#64) 8 =
      some (Int.ofBytes (wordBytes ra)))
    (P : MachineState → Prop)
    (next : ∀ flags, P (restored s rbx r14 flags, Int64.ofBitVec ra)) :
    Eventually (step e) P (s, base + 211) ∧
    Eventually (step e) P (s, base + 241) ∧
    Eventually (step e) P (s, base + 598) := by
  refine ⟨?_, ?_, ?_⟩
  · indices_count_step 43 using code
    indices_count_step 44 using code
    simp only [MachineData.load, Effects.All, savedBx, ofBytes_wordBytes]
    indices_count_step 45 using code
    simp only [MachineData.load, Effects.All, BitVec.add_assoc, BitVec.reduceAdd,
      saved14, ofBytes_wordBytes]
    indices_count_step 46 using code
    simp only [MachineData.load, Effects.All, BitVec.add_assoc, BitVec.reduceAdd,
      ret, ofBytes_wordBytes]
    apply Eventually.done
    simpa only [restored, BitVec.add_assoc, BitVec.reduceAdd] using next _
  · indices_count_step 51 using code
    indices_count_step 52 using code
    simp only [MachineData.load, Effects.All, savedBx, ofBytes_wordBytes]
    indices_count_step 53 using code
    simp only [MachineData.load, Effects.All, BitVec.add_assoc, BitVec.reduceAdd,
      saved14, ofBytes_wordBytes]
    indices_count_step 54 using code
    simp only [MachineData.load, Effects.All, BitVec.add_assoc, BitVec.reduceAdd,
      ret, ofBytes_wordBytes]
    apply Eventually.done
    simpa only [restored, BitVec.add_assoc, BitVec.reduceAdd] using next _
  · indices_count_step 150 using code
    indices_count_step 151 using code
    simp only [MachineData.load, Effects.All, savedBx, ofBytes_wordBytes]
    indices_count_step 152 using code
    simp only [MachineData.load, Effects.All, BitVec.add_assoc, BitVec.reduceAdd,
      saved14, ofBytes_wordBytes]
    indices_count_step 153 using code
    simp only [MachineData.load, Effects.All, BitVec.add_assoc, BitVec.reduceAdd,
      ret, ofBytes_wordBytes]
    apply Eventually.done
    simpa only [restored, BitVec.add_assoc, BitVec.reduceAdd] using next _

end SszX86.IndicesChunkCount

import SszX86.DelimitedBits
import SszX86.DelimitedStack

namespace SszX86.Delimited

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def bitSaveMem (s : MachineData) : DataMem :=
  let m := Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 16#64) 8 s.regs.r11.toBitVec.toInt
  Mem.storeInt m (s.regs.rsp.toBitVec - 16#64 + 8#64) 8 s.regs.r10.toBitVec.toInt

def bitSaved (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    dmem := bitSaveMem s
    regs := {s.regs with
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 16#64)
      r11 := UInt64.ofBitVec ((s.regs.rax.toBitVec.setWidth 32).setWidth 64)
      r10 := UInt64.ofBitVec (-1#64)}
    status := flags}

private theorem bit_wrapped_address (value : Int) :
    BitVec.ofInt 64 (value.bmod 18446744073709551616) = BitVec.ofInt 64 value := by
  simpa only [BitVec.toInt_ofInt, Nat.reducePow] using
    (BitVec.ofInt_toInt (x := BitVec.ofInt 64 value))

private theorem bit_lower_address (pointer : BitVec 64) :
    BitVec.ofInt 64 ((pointer.toInt + (-16)).bmod 18446744073709551616) =
      pointer - 16#64 := by
  have minus : BitVec.ofInt 64 (-16) = -(16#64) := by decide
  simp only [bit_wrapped_address, BitVec.ofInt_add, BitVec.ofInt_toInt,
    minus, ← BitVec.sub_eq_add_neg]

def bitPushed (s : MachineData) : MachineData :=
  {s with
    dmem := bitSaveMem s
    regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 16#64)}}

theorem bit_save_stores_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (hm : UintCodec.Large.Mapped s.dmem (s.regs.rsp.toBitVec - 16#64) 16)
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (bitPushed s, base + 57)) :
    Eventually (step e) P (s, base + 43) := by
  delimited_step 14 using hc
  delimited_step 15 using hc
  simp only [bit_lower_address]
  apply store_cps
  · apply mapped_load_zero (capacity := 16) (byteCount := 8)
    · exact hm
    · decide
  simp only [Effects.All]
  delimited_step 16 using hc
  simp only [BitVec.ofInt_add, bit_lower_address]
  apply store_cps
  · apply UintCodec.Large.mapped_load
      (dst := s.regs.rsp.toBitVec - 16#64)
      (capacity := 16) («offset» := 8) («width» := 8)
    · exact UintCodec.Large.mapped_store _ _ _ _ _ _ hm
    · decide
  simp only [Effects.All]
  simpa [bitPushed, bitSaveMem, BitVec.sub_eq_add_neg] using hp

def bitRegisters (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r11 := UInt64.ofBitVec ((s.regs.rax.toBitVec.setWidth 32).setWidth 64)
      r10 := UInt64.ofBitVec (-1#64)}
    status := flags}

theorem bit_registers_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (nonzero : s.regs.rax.toBitVec.setWidth 32 ≠ 0#32)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (bitRegisters s flags, base + 72)) :
    Eventually (step e) P (s, base + 57) := by
  delimited_step 17 using hc
  delimited_step 18 using hc
  constructor <;> delimited_step 19 using hc
  all_goals
    simp [nonzero, StatusFlags.from_result, Effects.All]
    delimited_step 20 using hc
    simpa [bitRegisters] using hp _

private theorem bit_saved_composition (s : MachineData) (flags : StatusFlags) :
    bitRegisters (bitPushed s) flags = bitSaved s flags := rfl

/-- The BSR lowering uses exactly the additional two stack words, restoring
both later. Its zero-input jump is ruled out by the already-read final byte. -/
theorem bit_save_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (hm : UintCodec.Large.Mapped s.dmem (s.regs.rsp.toBitVec - 16#64) 16)
    (nonzero : s.regs.rax.toBitVec.setWidth 32 ≠ 0#32)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (bitSaved s flags, base + 72)) :
    Eventually (step e) P (s, base + 43) := by
  apply bit_save_stores_cps e base hc s hm
  apply bit_registers_cps e base hc (bitPushed s) nonzero
  intro flags
  rw [bit_saved_composition]
  exact hp flags

def bitRestored (s : MachineData) (r10 r11 : BitVec 64) : MachineData :=
  {s with
    regs := {s.regs with
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 16#64)
      r10 := UInt64.ofBitVec r10
      r11 := UInt64.ofBitVec r11}}

theorem bit_restore_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (r10 r11 : BitVec 64)
    (lo : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (r11.toInt.take 64))
    (hi : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 = some (r10.toInt.take 64))
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (bitRestored s r10 r11, base + 103)) :
    Eventually (step e) P (s, base + 89) := by
  delimited_step 27 using hc
  delimited_load lo
  simp only [take_cast]
  delimited_step 28 using hc
  delimited_load hi
  simp only [take_cast]
  delimited_step 29 using hc
  simpa [bitRestored, BitVec.ofInt_add, BitVec.ofInt_toInt] using hp

end SszX86.Delimited

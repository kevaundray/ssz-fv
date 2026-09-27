import SszX86.DelimitedArenaExec

namespace SszX86.Delimited.Reservation
open SszX86.Delimited

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def committedMem (s : MachineData) : DataMem :=
  let m := Mem.storeInt s.dmem (s.regs.r8.toBitVec + 16#64) 8 s.regs.r10.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rax.toBitVec + s.regs.r9.toBitVec) 8 s.regs.r14.toBitVec.toInt
  Mem.storeInt m (s.regs.rax.toBitVec + s.regs.r9.toBitVec + 8#64) 8 s.regs.rbp.toBitVec.toInt

def committed (s : MachineData) : MachineData :=
  {s with
    dmem := committedMem s
    regs := {s.regs with
      r8 := UInt64.ofBitVec (s.regs.rax.toBitVec + s.regs.r9.toBitVec)
      r15 := 2}}

/-- The cursor is committed before the two exact limb stores and before the
Option discriminant load. Alignment padding is never written. -/
theorem commit_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData)
    (header : ∃ old, Mem.loadInt s.dmem (s.regs.r8.toBitVec + 16#64) 8 = some old)
    (payload : UintCodec.Large.Mapped s.dmem
      (s.regs.rax.toBitVec + s.regs.r9.toBitVec) 16)
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (committed s, base + 365)) :
    Eventually (step e) P (s, base + 342) := by
  delimited_step 79 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply store_cps
  · exact header
  simp only [Effects.All]
  delimited_step 80 using hc
  delimited_step 81 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply store_cps
  · apply mapped_load_zero (capacity := 16) (byteCount := 8)
    · exact UintCodec.Large.mapped_store _ _ _ _ _ _ payload
    · decide
  simp only [Effects.All]
  delimited_step 82 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
  apply store_cps
  · apply UintCodec.Large.mapped_load
      (dst := s.regs.rax.toBitVec + s.regs.r9.toBitVec)
      (capacity := 16) (offset := 8) («width» := 8)
    · exact UintCodec.Large.mapped_store _ _ _ _ _ _
        (UintCodec.Large.mapped_store _ _ _ _ _ _ payload)
    · decide
  simp only [Effects.All]
  delimited_step 83 using hc
  simpa [committed, committedMem, BitVec.add_assoc] using hp

/-- None still reaches this point after the sixteen-byte allocation. -/
theorem option_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (tag : BitVec 32)
    (hl : Mem.loadInt s.dmem s.regs.rsi.toBitVec 4 = some (tag.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if tag = 1#32 then base + 374 else base + 523)) :
    Eventually (step e) P (s, base + 365) := by
  have target := hc.targets ("delimited_u523", 523) (by decide)
  delimited_step 84 using hc
  delimited_load hl
  delimited_step 85 using hc
  by_cases one : tag = 1#32
  · simpa [one, StatusFlags.from_result, Effects.All] using hp _
  · have unequal : tag - 1#32 ≠ 0#32 := by
      intro hz
      apply one
      bv_omega
    simpa [one, unequal, target, StatusFlags.from_result, Effects.All] using hp _

end SszX86.Delimited.Reservation

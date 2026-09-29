import SszX86.CodecMeasurePartsReserveExec
import SszX86.CodecPlanSingletonMemory
import SszX86.EmitBitsMemory

namespace SszX86.CodecMeasureParts
open UintCodec

/-- Native order: publish the complete outer reservation cursor, then save its
pointer in the caller's local frame. Neither operation initializes a Plan slot. -/
def committedMem (s : MachineData) : DataMem :=
  Mem.storeInt
    (Mem.storeInt s.dmem (s.regs.r14.toBitVec + 16) 8 s.regs.rcx.toBitVec.toInt)
    (s.regs.rsp.toBitVec + 24) 8 (s.regs.rsi.toBitVec + s.regs.rax.toBitVec).toInt

def committed (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    rsi := UInt64.ofBitVec (s.regs.rsi.toBitVec + s.regs.rax.toBitVec),
    rbp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 64),
    r13 := UInt64.ofBitVec (s.regs.r13.toBitVec + 16), r12 := 0},
    dmem := committedMem s, status := flags}

/-- PC414's cursor store is executed before the first initializer at PC448. -/
theorem commit_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (header : Large.Mapped s.dmem (s.regs.r14.toBitVec + 16) 8)
    (local : Large.Mapped s.dmem (s.regs.rsp.toBitVec + 24) 8)
    (next : ∀ flags, Eventually (step e) P (committed s flags, base + 448)) :
    Eventually (step e) P (s, base + 414) := by
  codec_measure_parts_step 93 using code
  apply Delimited.store_cps
  · simpa only [BitVec.ofNat_zero, BitVec.add_zero] using
      Large.mapped_load s.dmem (s.regs.r14.toBitVec + 16) 8 0 8 header (by decide)
  simp only [Effects.All]
  codec_measure_parts_step 94 using code
  codec_measure_parts_step 95 using code
  apply Delimited.store_cps
  · have mapped := Large.mapped_store s.dmem (s.regs.rsp.toBitVec + 24)
      (s.regs.r14.toBitVec + 16) 8 8 s.regs.rcx.toBitVec.toInt local
    simpa only [BitVec.ofNat_zero, BitVec.add_zero] using
      Large.mapped_load _ (s.regs.rsp.toBitVec + 24) 8 0 8 mapped (by decide)
  simp only [Effects.All]
  codec_measure_parts_step 96 using code
  codec_measure_parts_step 97 using code
  codec_measure_parts_step 98 using code
  constructor
  · codec_measure_parts_step 99 using code
    simpa [committed, committedMem, Effects.All, StatusFlags.from_result] using next _
  · codec_measure_parts_step 99 using code
    simpa [committed, committedMem, Effects.All, StatusFlags.from_result] using next _

/-- The typed reservation cannot initialize even the first Plan by committing;
the exact memory frame permits only the arena cursor and one local pointer word. -/
theorem committed_frame (s : MachineData) :
    Emit.MemoryFrame s.dmem (committedMem s) (fun a =>
      Emit.InSpan a (s.regs.r14.toBitVec + 16) 8 ∨
      Emit.InSpan a (s.regs.rsp.toBitVec + 24) 8) := by
  intro a outside
  unfold committedMem
  rw [Emit.Bits.store_frame _ _ _ _ a (fun inside => outside (Or.inr inside))]
  exact Emit.Bits.store_frame _ _ _ _ a (fun inside => outside (Or.inl inside))

/-- Local bookkeeping does not undo or postpone the externally visible cursor
commit. In particular an initializer failure cannot roll this reservation back. -/
theorem committed_cursor (s : MachineData)
    (separate : CodecPlanSingleton.Apart (s.regs.r14.toBitVec + 16) 8
      (s.regs.rsp.toBitVec + 24) 8) :
    Mem.loadInt (committedMem s) (s.regs.r14.toBitVec + 16) 8 =
      some (s.regs.rcx.toNat : Int) := by
  unfold committedMem
  have preserved := CodecPlanSingleton.load_store_apart
    (Mem.storeInt s.dmem (s.regs.r14.toBitVec + 16) 8 s.regs.rcx.toBitVec.toInt)
    (s.regs.r14.toBitVec + 16) (s.regs.rsp.toBitVec + 24) 8 8 0 0 8 8
    (s.regs.rsi.toBitVec + s.regs.rax.toBitVec).toInt separate (by decide) (by decide)
  simp only [BitVec.ofNat_zero, BitVec.add_zero] at preserved
  rw [preserved]
  exact CodecPlanSingleton.stored_word _ _ _

end SszX86.CodecMeasureParts

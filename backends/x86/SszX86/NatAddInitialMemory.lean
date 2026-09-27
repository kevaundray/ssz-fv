import SszX86.NatAddWorkMemory
import SszX86.NatAddControl

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem ControlFrame.work {s t : MachineData} (frame : ControlFrame (pushedState s) t)
    (outcome : NatArithmetic.Outcome NatOperand) : WorkFrame s t.dmem outcome := by
  intro a output scratch
  rw [frame.memory]
  rfl

theorem ControlFrame.output_mapped {s t : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra)
    (frame : ControlFrame (pushedState s) t) : OutputMapped t := by
  change Large.Mapped t.dmem t.regs.rdi.toBitVec 68
  rw [frame.memory, frame.output]
  change Large.Mapped (pushedMem s) s.regs.rdi.toBitVec 68
  unfold pushedMem Delimited.pushedMem
  repeat' first | exact owned.output_mapped | apply Large.mapped_store

theorem ControlFrame.cursor {s t : MachineData} {left right : NatOperand}
    {address capacity used ra : BitVec 64} (owned : Owned s left right address capacity used ra)
    (frame : ControlFrame (pushedState s) t) :
    widthLoad t.dmem (s.regs.r9.toNat+16) 8 = some used.toNat := by
  have header := (pushed_header s left right address capacity used ra owned).2.2
  have sixteen : (16 : BitVec 64) = 16#64 := by decide
  rw [sixteen] at header
  rw [frame.memory]
  change widthLoad (pushedMem s) (s.regs.r9.toBitVec.toNat+16) 8 = some used.toNat
  simp only [widthLoad, width_address, header, Option.map_some, Int.toNat_natCast]

theorem ControlFrame.sp {s t : MachineData} (frame : ControlFrame (pushedState s) t) :
    t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 48 := by
  rw [frame.stack]
  rfl

theorem ControlFrame.original_simd {s t : MachineData} (frame : ControlFrame (pushedState s) t) :
    t.zmms = s.zmms := frame.simd

end SszX86.NatAdd

import SszX86.NatDivisionProtected
import SszX86.NatDivisionReturn

namespace SszX86.NatDivision
open SszNative
open UintCodec

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- All data facts at the single real epilogue. This is an internal physical
state assertion, discharged separately by each executed arithmetic path. -/
structure BeforeReturn (s : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64) (t : MachineData) : Prop where
  observed : NatArithmetic.DivisionResultAt (widthLoad t.dmem) s.regs.rdi.toNat
    (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).result
  written : ∀ r,
    (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).allocation = some r →
    NatMemory.wordsAt (widthLoad t.dmem) r.pointer
      (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).written
  frame : Frame s t.dmem
    (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat)
  cursor : widthLoad t.dmem (s.regs.r8.toNat + 16) 8 =
    some (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).used
  stack : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 56
  saved : SavedAt t.dmem t.regs.rsp.toBitVec s
  vectors : t.zmms = s.zmms
  return_slot : Mem.loadInt t.dmem s.regs.rsp.toBitVec 8 =
    some (Int.ofBytes (wordBytes ra))

/-- Every path executes the actual six POPs and RET before obtaining Post. -/
theorem finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (ready : BeforeReturn s operand divisor address capacity used ra t) :
    Eventually (step e) (Post s operand divisor address capacity used ra) (t, base + 456) := by
  apply epilogue_cps e base hc t s ra ready.saved
  · simpa only [ready.stack, BitVec.sub_add_cancel] using ready.return_slot
  intro flags
  apply Eventually.done
  have frame := exit_frame t s flags
  apply post_of_frame s operand divisor address capacity used ra _ owned
  · exact ready.observed
  · exact ready.written
  · refine ⟨rfl, exit_stack t s flags ready.stack, frame.rbx, frame.rbp,
      frame.r12, frame.r13, frame.r14, frame.r15, ?_, ?_⟩
    · exact frame.vectors.trans ready.vectors
    · exact ready.return_slot
  · exact ready.frame
  · exact ready.cursor

end SszX86.NatDivision

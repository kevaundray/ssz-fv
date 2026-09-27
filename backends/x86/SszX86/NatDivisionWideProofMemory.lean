import SszX86.NatDivisionFinish
import SszX86.NatDivisionFrame
import SszX86.NatDivisionPrologueMemory
import SszX86.NatDivisionOutputFinish
import SszX86.NatDivisionQuotient
import SszX86.NatDivisionPrepare
import SszX86.NatDivisionWidePhase
import SszX86.NatDivisionReserveMemory

namespace SszX86.NatDivision
open SszNative UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Physical facts shared by both publication branches, after arithmetic and
any allocation have actually executed. -/
structure WidePublication (s : MachineData) (operand : NatOperand)
    (divisor address capacity used : BitVec 64) (t : MachineData) : Prop where
  frame : Frame s t.dmem
    (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat)
  cursor : widthLoad t.dmem (s.regs.r8.toNat + 16) 8 =
    some (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).used
  saved : SavedAt t.dmem (s.regs.rsp.toBitVec - 56) s
  stack : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 56
  vectors : t.zmms = s.zmms
  output : t.regs.rbx = s.regs.rdi
  «mapped» : ResultMapped t

/-- Success publication and the real epilogue consume exact physical facts;
all written limbs are retained separately from the visible quotient. -/
theorem wide_publish_success (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (operand quotient : NatOperand)
    (divisor address capacity used ra remainder : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (physical : WidePublication s operand divisor address capacity used t)
    (reason : t.regs.r14 = 0)
    (pointer : t.regs.rdi.toBitVec = quotient.pointer)
    (payload : t.regs.rcx.toBitVec = quotient.payload)
    (rem : t.regs.r15.toBitVec - t.regs.rax.toBitVec * t.regs.r13.toBitVec = remainder)
    (result : (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).result =
      .ok (quotient, remainder))
    (stored : quotient.At (widthLoad
      (resultSuccessMem t.dmem s.regs.rdi.toBitVec quotient.pointer quotient.payload remainder)))
    (written : ∀ r,
      (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).allocation = some r →
      NatMemory.wordsAt (widthLoad
        (resultSuccessMem t.dmem s.regs.rdi.toBitVec quotient.pointer quotient.payload remainder)) r.pointer
        (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).written) :
    Eventually (step e) (Post s operand divisor address capacity used ra) (t, base + 358) := by
  apply result_success_cps e base hc t physical.mapped reason
  intro flags
  apply finish_cps e base hc s (resultSuccessState t flags) operand divisor address capacity used ra owned
  have memory : (resultSuccessState t flags).dmem =
      resultSuccessMem t.dmem s.regs.rdi.toBitVec quotient.pointer quotient.payload remainder := by
    simp only [resultSuccessState, physical.output, pointer, payload, rem]
  have frame := physical.frame.result_success owned.output_bound quotient.pointer quotient.payload remainder
  have outframe := result_success_mem_frame t.dmem s.regs.rdi.toBitVec
    quotient.pointer quotient.payload remainder
  refine ⟨?_, ?_, ?_, ?_, physical.stack, ?_, physical.vectors, ?_⟩
  · rw [memory, result]
    exact result_success_observed t.dmem s.regs.rdi.toBitVec remainder quotient stored
  · rw [memory]
    exact written
  · rw [memory]
    exact frame
  · rw [memory, result_only_cursor s operand divisor address capacity used ra owned _ _ outframe]
    exact physical.cursor
  · change SavedAt (resultSuccessState t flags).dmem t.regs.rsp.toBitVec s
    rw [memory, physical.stack]
    exact result_only_saved s operand divisor address capacity used ra owned _ _
      (s.regs.rsp.toBitVec - 56) rfl outframe physical.saved
  · rw [memory]
    exact frame.return_slot owned

/-- Failure publication clears the real output and then restores the caller. -/
theorem wide_publish_error (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (physical : WidePublication s operand divisor address capacity used t)
    (outcome : SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat =
      NatArithmetic.unchanged used.toNat (.error .scratchExhausted)) :
    Eventually (step e) (Post s operand divisor address capacity used ra) (t, base + 379) := by
  apply result_error_cps e base hc t physical.mapped
  intro flags
  apply finish_cps e base hc s (resultErrorState t flags) operand divisor address capacity used ra owned
  have memory : (resultErrorState t flags).dmem = resultErrorMem t.dmem s.regs.rdi.toBitVec := by
    simp only [resultErrorState, physical.output]
  have frame := physical.frame.result_error owned.output_bound
  have outframe := result_error_mem_frame t.dmem s.regs.rdi.toBitVec
  refine ⟨?_, ?_, ?_, ?_, physical.stack, ?_, physical.vectors, ?_⟩
  · rw [memory, outcome]
    exact result_error_observed t.dmem s.regs.rdi.toBitVec
  · simp [outcome, NatArithmetic.unchanged]
  · rw [memory]
    exact frame
  · rw [memory, result_only_cursor s operand divisor address capacity used ra owned _ _ outframe]
    exact physical.cursor
  · change SavedAt (resultErrorState t flags).dmem t.regs.rsp.toBitVec s
    rw [memory, physical.stack]
    exact result_only_saved s operand divisor address capacity used ra owned _ _
      (s.regs.rsp.toBitVec - 56) rfl outframe physical.saved
  · rw [memory]
    exact frame.return_slot owned

end SszX86.NatDivision

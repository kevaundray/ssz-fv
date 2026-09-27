import SszX86.NatDivisionLargeProofPrepare
import SszX86.NatDivisionReserveGuard
import SszX86.NatDivisionOutputFinish
import SszX86.NatDivisionFinish

namespace SszX86.NatDivision
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Every failed large reservation restores the spilled output pointer, writes
the actual private ScratchExhausted record, and executes all six POPs and RET.
The state at PC205 is otherwise opaque: only its unchanged physical memory,
stack pointer, and SIMD frame are required. -/
theorem large_reserve_failure_finish (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (count : 2 < operand.wordCount)
    (failed : Arena.reserve address.toNat capacity.toNat used.toNat operand.wordCount = none)
    (memory : t.dmem = largeSpillMem s)
    (stack : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 56#64)
    (vectors : t.zmms = s.zmms) :
    Eventually (step e) (Post s operand divisor address capacity used ra) (t, base + 205) := by
  have model := SszNative.NatDivision.phase_reserve_failure operand divisor
    address.toNat capacity.toNat used.toNat owned.divisor_nonzero owned.divisor_ne_one count failed
  have unallocated :
      (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).allocation = none := by
    rw [model]
    rfl
  have savedBefore : SavedAt (largeSpillMem s) (s.regs.rsp.toBitVec - 56#64) s :=
    savedAt_scratch (pushedMem s) _ s s.regs.rdi.toBitVec.toInt (pushed_saved s)
  apply Reservation.Large.failure_cps e base hc t s.regs.rdi.toBitVec
  · have spill := large_spill_output s
    change Mem.loadInt (largeSpillMem s) (s.regs.rsp.toBitVec - 56#64) 8 =
      some (s.regs.rdi.toNat : Int) at spill
    simpa only [memory, stack, UInt64.toNat_toBitVec] using spill
  let restored : MachineData := {t with regs := {t.regs with rbx := s.regs.rdi}}
  change Eventually (step e) (Post s operand divisor address capacity used ra) (restored, base + 379)
  apply result_error_cps e base hc restored
  · change Large.Mapped t.dmem s.regs.rdi.toBitVec 68
    rw [memory]
    exact large_spill_mapped s _ _ owned.output_mapped
  intro flags
  have finalFrame : Frame s (resultErrorState restored flags).dmem
      (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat) := by
    simpa only [resultErrorState, restored, memory] using
      (large_spill_frame s owned.stack_low
        (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat)).result_error
        owned.output_bound
  apply finish_cps e base hc s (resultErrorState restored flags) operand
    divisor address capacity used ra owned
  refine ⟨?_, ?_, finalFrame, ?_, ?_, ?_, ?_, ?_⟩
  · rw [model]
    simpa only [NatArithmetic.unchanged, resultErrorState, restored, memory,
      UInt64.toNat_toBitVec] using result_error_observed (largeSpillMem s) s.regs.rdi.toBitVec
  · intro r allocated
    rw [unallocated] at allocated
    contradiction
  · have cursorLoad := finalFrame.cursor_unallocated owned unallocated
    change Mem.loadInt (resultErrorState restored flags).dmem
      (s.regs.r8.toBitVec + 16#64) 8 = some (used.toNat : Int) at cursorLoad
    rw [model]
    simpa only [NatArithmetic.unchanged, widthLoad, ← UInt64.toNat_toBitVec,
      width_address, Option.map_some, Int.toNat_natCast] using congrArg (Option.map Int.toNat) cursorLoad
  · exact stack
  · have savedAfter := result_only_saved s operand divisor address capacity used ra owned
      (largeSpillMem s) (resultErrorMem (largeSpillMem s) s.regs.rdi.toBitVec)
      (s.regs.rsp.toBitVec - 56#64) rfl
      (result_error_mem_frame (largeSpillMem s) s.regs.rdi.toBitVec) savedBefore
    simpa only [resultErrorState, restored, memory, stack] using savedAfter
  · exact vectors
  · exact finalFrame.return_slot owned

end SszX86.NatDivision

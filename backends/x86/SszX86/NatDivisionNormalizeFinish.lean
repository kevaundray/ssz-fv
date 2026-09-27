import SszX86.NatDivisionNormalizePhase
import SszX86.NatDivisionOutputFinish
import SszX86.NatDivisionFinish

namespace SszX86.NatDivision
open SszNative UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Physical handoff at PC477, after the entire reverse quotient pass. The
stored list is the complete allocation, not the normalized returned prefix. -/
structure NormalizeReady (s : MachineData) (operand : NatOperand)
    (divisor address capacity used : BitVec 64) (words : List (BitVec 64))
    (reservation : Arena.Reservation) (t : MachineData) : Prop where
  allocated : (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).allocation =
    some reservation
  written : (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).written = words
  result : (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).result =
    .ok (NatOperand.fromWords t.regs.r14.toBitVec words, t.regs.r15.toBitVec)
  pointer : reservation.pointer = t.regs.r14.toNat
  stored : (NatOperand.large t.regs.r14.toBitVec words).At (widthLoad t.dmem)
  apart : Body.Apart t.regs.r14.toNat (8*words.length) s.regs.rdi.toNat 68
  count : t.regs.r13.toBitVec = BitVec.ofNat 64 (words.length+1)
  spill : Mem.loadInt t.dmem t.regs.rsp.toBitVec 8 = some (s.regs.rdi.toNat : Int)
  «mapped» : Large.Mapped t.dmem s.regs.rdi.toBitVec 68
  frame : Frame s t.dmem
    (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat)
  cursor : widthLoad t.dmem (s.regs.r8.toNat+16) 8 =
    some (SszNative.NatDivision.run operand divisor address.toNat capacity.toNat used.toNat).used
  saved : SavedAt t.dmem t.regs.rsp.toBitVec s
  stack : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 56
  vectors : t.zmms = s.zmms

/-- The late large-path handoff executes normalization, publishes the exact
private result, restores saved registers, and executes the real RET. -/
theorem normalize_finish (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64) (words : List (BitVec 64))
    (reservation : Arena.Reservation)
    (owned : Owned s operand divisor address capacity used ra)
    (ready : NormalizeReady s operand divisor address capacity used words reservation t) :
    Eventually (step e) (Post s operand divisor address capacity used ra) (t, base + 477) := by
  let u : MachineData := {t with regs := {t.regs with rbx := s.regs.rdi}}
  apply normalize_entry_cps e base hc t s.regs.rdi.toBitVec ready.spill
  change Eventually (step e) (Post s operand divisor address capacity used ra) (u, base + 496)
  have initial := normalizeScanState_initial u
  have count : u.regs.r13.toBitVec = BitVec.ofNat 64 (words.length+1) := ready.count
  rw [count] at initial
  rw [← initial]
  have bound : words.length+1 < 2^64 := by
    have extent := ready.stored.2.2.1
    omega
  apply normalize_result_cps e base hc u words bound ready.mapped
  · intro i
    simpa only [u, width_address] using widthLoad_eq t.dmem _ _ _ (ready.stored.2.2.2 i)
  intro flags
  have observed := normalized_result_memory u words flags owned.output_bound ready.apart ready.stored
  have memory : (normalizedResultState u words flags).dmem =
      resultSuccessMem t.dmem s.regs.rdi.toBitVec
        (NatOperand.fromWords t.regs.r14.toBitVec words).pointer
        (NatOperand.fromWords t.regs.r14.toBitVec words).payload t.regs.r15.toBitVec := rfl
  have frame := ready.frame.result_success owned.output_bound
    (NatOperand.fromWords t.regs.r14.toBitVec words).pointer
    (NatOperand.fromWords t.regs.r14.toBitVec words).payload t.regs.r15.toBitVec
  have outframe := result_success_mem_frame t.dmem s.regs.rdi.toBitVec
    (NatOperand.fromWords t.regs.r14.toBitVec words).pointer
    (NatOperand.fromWords t.regs.r14.toBitVec words).payload t.regs.r15.toBitVec
  apply finish_cps e base hc s (normalizedResultState u words flags) operand
    divisor address capacity used ra owned
  refine ⟨?_, ?_, ?_, ?_, ready.stack, ?_, ready.vectors, ?_⟩
  · rw [ready.result]
    exact observed.2
  · intro allocated hallocated
    have equal : allocated = reservation := by
      rw [ready.allocated] at hallocated
      exact (Option.some.inj hallocated).symm
    subst allocated
    rw [ready.written, ready.pointer]
    exact observed.1
  · rw [memory]
    exact frame
  · rw [memory, result_only_cursor s operand divisor address capacity used ra owned _ _ outframe]
    exact ready.cursor
  · change SavedAt (normalizedResultState u words flags).dmem t.regs.rsp.toBitVec s
    rw [memory]
    exact result_only_saved s operand divisor address capacity used ra owned _ _ _ ready.stack outframe ready.saved
  · rw [memory]
    exact frame.return_slot owned

end SszX86.NatDivision

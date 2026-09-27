import SszX86.NatDivisionWideProofMemory

namespace SszX86.NatDivision
open SszNative UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Physical arithmetic state after the actual embedded call returns.  The
universal frame records that this stage has written only its activation. -/
structure WideCalled (s : MachineData) (operand : NatOperand)
    (divisor address capacity used : BitVec 64) (t : MachineData) : Prop where
  frame : ∀ outcome, Frame s t.dmem outcome
  header : Reservation.Small.Header t address capacity used
  «mapped» : ResultMapped t
  arena_mapped : Large.Mapped t.dmem address capacity.toNat
  saved : SavedAt t.dmem (s.regs.rsp.toBitVec - 56) s
  stack : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 56
  vectors : t.zmms = s.zmms
  output : t.regs.rbx = s.regs.rdi
  arena : t.regs.r12 = s.regs.r8
  divisor_reg : t.regs.r13.toBitVec = divisor
  low : t.regs.r15.toBitVec = operand.words[0]?.getD 0
  reason : t.regs.r14 = 0
  quotient : Udivti3.value t.regs.rax.toBitVec t.regs.rdx.toBitVec = operand.value / divisor.toNat

theorem WideCalled.cursor {s t : MachineData} {operand : NatOperand}
    {divisor address capacity used : BitVec 64}
    (called : WideCalled s operand divisor address capacity used t) :
    widthLoad t.dmem (s.regs.r8.toNat + 16) 8 = some used.toNat := by
  have hload := called.header.used_load
  rw [called.arena] at hload
  simp only [widthLoad, ← UInt64.toNat_toBitVec, width_address, hload,
    Option.map_some, Int.toNat_natCast]

/-- Loading the descriptor after CALL is justified by the activation frame,
not by an assumption about the source model's eventual allocation. -/
theorem wide_call_header_load (s : MachineData) (operand : NatOperand)
    (divisor address capacity used ra ret : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (off count : Nat) (inside : off + count ≤ 24) :
    Mem.loadInt (Mem.storeInt (pushedMem s) (s.regs.rsp.toBitVec - 64) 8 ret.toInt)
      (s.regs.r8.toBitVec + BitVec.ofNat 64 off) count =
    Mem.loadInt s.dmem (s.regs.r8.toBitVec + BitVec.ofNat 64 off) count := by
  have bound := owned.header_bound
  have apart := owned.header_stack
  have hload := activation_load_congr s owned.stack_low (pushedMem s)
    (Mem.storeInt (pushedMem s) (s.regs.rsp.toBitVec - 64) 8 ret.toInt)
    (fun a outside => stack_store_frame _ _ a 64 64 8 ret.toInt
      (by decide) (by decide) outside)
    (s.regs.r8.toNat + off) count (by omega)
    (by unfold Body.Apart at *; omega)
  have hload' : Mem.loadInt
      (Mem.storeInt (pushedMem s) (s.regs.rsp.toBitVec - 64) 8 ret.toInt)
      (s.regs.r8.toBitVec + BitVec.ofNat 64 off) count =
      Mem.loadInt (pushedMem s) (s.regs.r8.toBitVec + BitVec.ofNat 64 off) count := by
    simpa only [← UInt64.toNat_toBitVec, width_address] using hload
  exact hload'.trans (owned.pushed_header_load off count inside)

theorem wide_called_of_divided (s t : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64) (ret : Int64)
    (owned : Owned s operand divisor address capacity used ra)
    (count : operand.wordCount ≤ 2)
    (prepared : WidePrepared (prologueState s) operand.words t)
    (u : MachineState) (divided : Divided t ret u) :
    WideCalled s operand divisor address capacity used u.1 := by
  have stack : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 56 := by
    rw [prepared.stack]
    rfl
  have callslot : t.regs.rsp.toBitVec - 8 = s.regs.rsp.toBitVec - 64 := by
    rw [stack]
    bv_omega
  have memory : u.1.dmem =
      Mem.storeInt (pushedMem s) (s.regs.rsp.toBitVec - 64) 8 ret.toBitVec.toInt := by
    rw [divided.memory]
    simp only [callState, prepared.memory, callslot, prologueState, pushedState]
  have output : u.1.regs.rbx = s.regs.rdi := divided.output.trans prepared.output
  have arena : u.1.regs.r12 = s.regs.r8 := divided.arena.trans prepared.arena
  have divisor_reg : u.1.regs.r13.toBitVec = divisor := by
    rw [divided.divisor, prepared.divisor]
    exact owned.divisor_register
  refine ⟨?_, ?_, ?_, ?_, ?_, divided.stack.trans stack,
    divided.vectors.trans prepared.vectors, output, arena, divisor_reg,
    ?_, divided.reason, ?_⟩
  · intro outcome
    rw [memory]
    exact (pushed_outcome_frame s owned.stack_low outcome).store_stack
      owned.stack_low 64 8 ret.toBitVec.toInt (by decide) (by decide)
  · constructor
    · rw [memory, arena]
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
        (wide_call_header_load s operand divisor address capacity used ra ret.toBitVec owned 0 8
          (by decide)).trans (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using owned.address_load)
    · rw [memory, arena]
      exact (wide_call_header_load s operand divisor address capacity used ra ret.toBitVec owned 8 8
        (by decide)).trans owned.capacity_load
    · rw [memory, arena]
      exact (wide_call_header_load s operand divisor address capacity used ra ret.toBitVec owned 16 8
        (by decide)).trans owned.used_load
  · change Large.Mapped u.1.dmem u.1.regs.rbx.toBitVec 68
    rw [output, divided.memory]
    apply call_mapped
    rw [prepared.memory]
    exact owned.prologue_output_mapped
  · rw [divided.memory]
    apply call_mapped
    rw [prepared.memory]
    exact owned.prologue_arena_mapped
  · rw [divided.memory, ← stack]
    apply call_saved
    rw [prepared.memory, prepared.stack]
    exact prologue_saved s
  · rw [divided.low]
    exact prepared.low
  · have quotient := divided.quotient
    rw [prepared.low, prepared.high, prepared.divisor] at quotient
    rw [owned.prologue_retained_divisor, input_pair operand count] at quotient
    exact quotient

end SszX86.NatDivision

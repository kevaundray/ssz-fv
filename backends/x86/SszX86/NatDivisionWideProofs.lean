import SszX86.NatDivisionWideProofUnallocated
import SszX86.NatDivisionWideProofAllocated

namespace SszX86.NatDivision
open SszNative UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The TEST/JNE branch only changes flags, preserving the physical call
summary without unfolding the embedded divider's machine state. -/
theorem WideCalled.flagged {s t : MachineData} {operand : NatOperand}
    {divisor address capacity used : BitVec 64}
    (called : WideCalled s operand divisor address capacity used t) (flags : StatusFlags) :
    WideCalled s operand divisor address capacity used {t with status := flags} :=
  ⟨called.frame,
    ⟨called.header.address_load, called.header.capacity_load, called.header.used_load⟩,
    called.mapped, called.arena_mapped, called.saved,
    called.stack, called.vectors, called.output, called.arena, called.divisor_reg,
    called.low, called.reason, called.quotient⟩

/-- Complete native arithmetic for every operand with at most two significant
words, including long original borrowed representations with high zero limbs.
The real CALL and divider RET, checked reserve, publication, and final RET are
composed before obtaining the exact owned result contract. -/
theorem wide_phase (e : Executable) (base : Int64) (hc : CodeAt e base)
    (hdiv : Udivti3.Embedded.CodeAt e (base + 160352))
    (s t : MachineData) (operand : NatOperand)
    (divisor address capacity used ra : BitVec 64)
    (owned : Owned s operand divisor address capacity used ra)
    (count : operand.wordCount ≤ 2)
    (prepared : WidePrepared (prologueState s) operand.words t) :
    Eventually (step e) (Post s operand divisor address capacity used ra) (t, base + 250) := by
  have divisor_reg : t.regs.r13.toBitVec = divisor := by
    rw [prepared.divisor]
    exact owned.prologue_retained_divisor
  have stack : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 56 := by
    rw [prepared.stack]
    rfl
  have callMapped : ∃ old, Mem.loadInt t.dmem (t.regs.rsp.toBitVec - 8) 8 = some old := by
    have slot : t.regs.rsp.toBitVec - 8 = s.regs.rsp.toBitVec - 64 := by
      rw [stack]
      bv_omega
    rw [slot, prepared.memory]
    exact activation_load _ s.regs.rsp.toBitVec 64 owned.prologue_activation_mapped
      (by decide) (by decide)
  apply wide_call_cps e base hc hdiv t
    (by rw [divisor_reg]; have lower := owned.divisor_lower; omega) callMapped
  intro state divided
  obtain ⟨u, pc⟩ := state
  have called := wide_called_of_divided s t operand divisor address capacity used ra
    (base + 267) owned count prepared (u, pc) divided
  have pcEq : pc = base + 267 := divided.pc
  subst pc
  apply quotient_dispatch_cps e base hc u
  · intro high flags
    exact wide_small_cps e base hc s u operand divisor address capacity used ra
      owned count called high flags
  · intro high flags
    have flagged := called.flagged flags
    apply Reservation.Small.reservation_cps e base hc {u with status := flags}
      address capacity used flagged.header flagged.arena_mapped
    intro state reserved
    obtain ⟨v, pc⟩ := state
    obtain ⟨frame, failure | success⟩ := reserved
    · obtain ⟨failure, pcEq, memory⟩ := failure
      change pc = base + 379 at pcEq
      subst pc
      exact wide_reservation_failure_cps e base hc s {u with status := flags} v operand
        divisor address capacity used ra owned count flagged high failure frame memory
    · obtain ⟨allocation, success, pcEq, outputFlags, stateEq⟩ := success
      change pc = base + 358 at pcEq
      subst pc
      change v = Reservation.Small.reservedState {u with status := flags}
        address used outputFlags at stateEq
      subst v
      exact wide_reserved_cps e base hc s {u with status := flags} operand
        divisor address capacity used ra owned count flagged high allocation success outputFlags

end SszX86.NatDivision

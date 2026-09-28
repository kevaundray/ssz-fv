import SszX86.NatMulReserve

namespace SszX86.NatMul.Reservation
open UintCodec
open SszNative
open Emit (MemoryFrame InSpan)

abbrev initializedState (s : MachineData) (address used : BitVec 64)
    (guardFlags fillFlags : StatusFlags) :=
  preparedState (allocatedState s address used guardFlags) fillFlags

def Changed (s : MachineData) (address used : BitVec 64) (a : BitVec 64) : Prop :=
  Written s a ∨
  InSpan a (address + BitVec.ofNat 64 (Arena.start address.toNat used.toNat)) (8 * total s) ∨
  InSpan a (s.regs.rsp.toBitVec - 8#64) 8

/-- The complete memory frame includes only the exact cursor/local spills,
allocated destination, and the real CALL's return slot. -/
theorem initialized_frame (s : MachineData) (address used : BitVec 64)
    (guardFlags fillFlags : StatusFlags) (ra : BitVec 64) (t : MachineState)
    (post : MemsetCall.Post (initializedState s address used guardFlags fillFlags) ra (8 * total s) t) :
    MemoryFrame s.dmem t.1.dmem (Changed s address used) := by
  intro a outside
  have helperOutside : ¬ (InSpan a
      (initializedState s address used guardFlags fillFlags).regs.rdi.toBitVec (8 * total s) ∨
      InSpan a ((initializedState s address used guardFlags fillFlags).regs.rsp.toBitVec - 8) 8) := by
    intro inside
    rcases inside with output | stack
    · apply outside
      exact Or.inr (Or.inl (by
        simpa [initializedState, preparedState, allocatedState, reservedState, countState] using output))
    · exact outside (Or.inr (Or.inr stack))
  rw [post.frame a helperOutside]
  apply prepared_frame (allocatedState s address used guardFlags) a
  intro inside
  exact outside (Or.inl (by
    simpa [Written, allocatedState, reservedState, countState] using inside))

/-- Extract the actual helper-return register contract at the loop entry. -/
theorem initialized_registers (s : MachineData) (base : Int64) (address used : BitVec 64)
    (guardFlags fillFlags : StatusFlags) (t : MachineState)
    (post : MemsetCall.Post (initializedState s address used guardFlags fillFlags)
      (base + 493).toBitVec (8 * total s) t) :
    t.2 = base + 493 ∧
    t.1.regs.rsp = s.regs.rsp ∧ t.1.zmms = s.zmms ∧
    t.1.regs.r12 = s.regs.r12 ∧ t.1.regs.r13 = s.regs.r13 ∧
    t.1.regs.r10 = s.regs.r10 ∧ t.1.regs.rcx = s.regs.rcx ∧
    t.1.regs.rbp.toBitVec = s.regs.r12.toBitVec - s.regs.r10.toBitVec ∧
    t.1.regs.r14.toBitVec = s.regs.r13.toBitVec + s.regs.r12.toBitVec ∧
    t.1.regs.r15 = 0 ∧
    t.1.regs.rbx.toBitVec = address + BitVec.ofNat 64 (Arena.start address.toNat used.toNat) ∧
    t.1.regs.rax.toBitVec = address + BitVec.ofNat 64 (Arena.start address.toNat used.toNat) := by
  have preserved := post.returned.2.2.2.2
  have r12 := preserved .r12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have r13 := preserved .r13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have r10 := preserved .r10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have rcx := preserved .rcx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have rbp := preserved .rbp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have r14 := preserved .r14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have r15 := preserved .r15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have rbx := preserved .rbx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have rax := post.returned.2.1
  have rsp := post.returned.2.2.1
  have zmms := post.returned.2.2.2.1
  have pc := post.returned.1
  simp only [initializedState, MemsetCall.callState, Emit.callState, preparedState,
    allocatedState, reservedState, countState, Reg64s.get64,
    UInt64.toBitVec_ofBitVec, UInt64.toBitVec_ofNat'] at *
  refine ⟨by simpa using pc, UInt64.toBitVec_inj.mp (by simpa using rsp), zmms,
    r12, r13, r10, rcx, ?_, ?_, r15, ?_, ?_⟩
  · simpa only [UInt64.toBitVec_ofBitVec] using congrArg UInt64.toBitVec rbp
  · simpa only [UInt64.toBitVec_ofBitVec] using congrArg UInt64.toBitVec r14
  · simpa only [UInt64.toBitVec_ofBitVec, UInt64.toBitVec_ofNat'] using congrArg UInt64.toBitVec rbx
  · simpa only [UInt64.toBitVec_ofBitVec, UInt64.toBitVec_ofNat'] using congrArg UInt64.toBitVec rax

end SszX86.NatMul.Reservation

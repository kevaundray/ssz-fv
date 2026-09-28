import SszX86.BitVectorNarrowOwned

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- Actual optional-rounding ABI, with all helper ownership derived from the
reached physical caller memory and the quotient's proven allocation provenance. -/
theorem add_owned (s t : MachineData) (saved : Saved) (length quotient : NatOperand)
    (data : Ssz.Bytes) (address capacity used ra : BitVec 64)
    (owned : Owned {s with dmem := t.dmem} saved length data address capacity used)
    (output : t.regs.rdi.toBitVec = s.regs.rsp.toBitVec + 16#64)
    (stack : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64)
    (arena : t.regs.r9 = s.regs.rbx)
    (leftPointer : t.regs.rsi.toBitVec = quotient.pointer)
    (leftPayload : t.regs.rdx.toBitVec = quotient.payload)
    (rightPointer : t.regs.rcx.toBitVec = 0#64)
    (rightPayload : t.regs.r8.toBitVec = 1#64)
    (stored : quotient.At (widthLoad t.dmem))
    (protectedOperand : OperandProtected s address capacity used quotient)
    (ret : Mem.loadInt t.dmem t.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    NatAdd.Owned t quotient (.small 1) address capacity used ra := by
  have low : 72 ≤ s.regs.rsp.toNat := owned.stack_low
  have high : s.regs.rsp.toNat + 368 ≤ 2^64 := owned.stack_bound
  have lowBV : 72 ≤ s.regs.rsp.toBitVec.toNat := low
  have highBV : s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64 := high
  have outNat : t.regs.rdi.toNat = s.regs.rsp.toNat + 16 := by
    change t.regs.rdi.toBitVec.toNat = s.regs.rsp.toBitVec.toNat + 16
    rw [output]
    bv_omega
  have spNat : t.regs.rsp.toNat = s.regs.rsp.toNat - 8 := by
    change t.regs.rsp.toBitVec.toNat = s.regs.rsp.toBitVec.toNat - 8
    rw [stack]
    bv_omega
  have arenaWork : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
      (s.regs.rsp.toNat - 72) 296 := owned.arena_work
  have headerWork : Body.Apart s.regs.rbx.toNat 24 (s.regs.rsp.toNat - 72) 296 :=
    owned.header_work
  have stackMapped : Large.Mapped t.dmem (t.regs.rsp.toBitVec - 48) 48 := by
    have part := mapped_subrange t.dmem (s.regs.rsp.toBitVec - 72#64) workSize 16 48
      owned.work_mapped (by decide)
    have location : s.regs.rsp.toBitVec - 72#64 + BitVec.ofNat 64 16 = t.regs.rsp.toBitVec - 48 := by
      rw [stack]
      bv_omega
    rw [location] at part
    exact part
  refine {
    left_pointer := leftPointer
    left_payload := leftPayload
    right_pointer := rightPointer
    right_payload := rightPayload
    left_at := stored
    right_at := trivial
    left_owned := ?_
    right_owned := trivial
    output_bound := by omega
    output_mapped := workspace_output_mapped s t 68 (by decide) owned.work_mapped output
    return_bound := by omega
    return_load := ret
    stack_low := by omega
    stack_mapped := stackMapped
    output_return := by unfold Body.Apart; omega
    output_stack := by unfold Body.Apart; omega
    header_bound := by simpa only [arena] using owned.header_bound
    address_load := by simpa only [arena] using owned.address_load
    capacity_load := by simpa only [arena] using owned.capacity_load
    used_load := by simpa only [arena] using owned.used_load
    arena_bound := owned.arena_bound
    used_bound := owned.used_bound
    arena_nonzero := owned.arena_nonzero
    arena_mapped := owned.arena_mapped
    arena_output := ?_
    arena_stack := ?_
    arena_return := ?_
    arena_header := by simpa only [arena] using owned.arena_header
    header_output := ?_
    header_stack := ?_
    cursor_return := ?_ }
  · cases quotient with
    | small limb => trivial
    | large pointer words =>
      change NatAdd.Protected t address capacity used pointer.toNat (8 * words.length)
      refine ⟨protectedOperand.bound, ?_, ?_, ?_, protectedOperand.arena⟩
      · have apart := protectedOperand.work
        unfold Body.Apart workStart workSize at apart
        unfold Body.Apart
        omega
      · have apart := protectedOperand.work
        unfold Body.Apart workStart workSize at apart
        unfold Body.Apart
        omega
      · simpa only [arena] using protectedOperand.cursor
  · have apart := arenaWork
    unfold Body.Apart at apart
    unfold Body.Apart
    omega
  · have apart := arenaWork
    unfold Body.Apart at apart
    unfold Body.Apart
    omega
  · have apart := arenaWork
    unfold Body.Apart at apart
    unfold Body.Apart
    omega
  · have apart := headerWork
    unfold Body.Apart at apart
    rw [arena]
    unfold Body.Apart
    omega
  · have apart := headerWork
    unfold Body.Apart at apart
    rw [arena]
    unfold Body.Apart
    omega
  · have apart := headerWork
    unfold Body.Apart at apart
    rw [arena]
    unfold Body.Apart
    omega

end SszX86.BitVector

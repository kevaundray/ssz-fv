import SszX86.BitVectorEntryMemory

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Helper ownership is derived from the initial caller's physical spans, not
assumed for a reached or hypothetical execution state. -/
theorem division_owned (s : MachineData) (saved : Saved) (length : NatOperand)
    (data : Ssz.Bytes) (address capacity used ra : BitVec 64)
    (owned : Owned s saved length data address capacity used) :
    NatDivision.Owned (divisionReady s length ra) length 8 address capacity used ra := by
  let t := divisionReady s length ra
  have out : t.regs.rdi.toBitVec = s.regs.rsp.toBitVec + 16#64 := by
    simp only [t, divisionReady, callState, NatDivision.callState, entryState, UInt64.toBitVec_ofBitVec]
  have stack : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64 := by
    simp only [t, divisionReady, callState, NatDivision.callState, entryState, UInt64.toBitVec_ofBitVec]
    rw [show (8 : BitVec 64) = 8#64 by decide]
  have arena : t.regs.r8 = s.regs.rbx := rfl
  have low := owned.stack_low
  have high := owned.stack_bound
  have outNat : t.regs.rdi.toNat = s.regs.rsp.toNat + 16 := by
    change t.regs.rdi.toBitVec.toNat = s.regs.rsp.toBitVec.toNat + 16
    rw [out]
    have highBV : s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64 := high
    bv_omega
  have stackNat : t.regs.rsp.toNat = s.regs.rsp.toNat - 8 := by
    change t.regs.rsp.toBitVec.toNat = s.regs.rsp.toBitVec.toNat - 8
    rw [stack]
    have lowBV : 72 ≤ s.regs.rsp.toBitVec.toNat := low
    bv_omega
  have headerWork := owned.header_work
  have arenaWork := owned.arena_work
  have workMapped := initial_mapped s length ra _ _ owned.work_mapped
  have headerRead (off : Nat) (within : off + 8 ≤ 24) :
      Mem.loadInt t.dmem (t.regs.r8.toBitVec + BitVec.ofNat 64 off) 8 =
        Mem.loadInt s.dmem (s.regs.rbx.toBitVec + BitVec.ofNat 64 off) 8 := by
    exact initial_offset_load s saved length data address capacity used ra owned
      s.regs.rbx.toBitVec 24 off 8 owned.header_bound owned.header_work within
  refine {
    operand_pointer := ?_
    operand_payload := ?_
    divisor_register := ?_
    divisor_lower := by decide
    operand_at := initial_operand s saved length data address capacity used ra owned
    operand_owned := ?_
    output_bound := ?_
    output_mapped := ?_
    return_bound := ?_
    return_load := ?_
    stack_low := ?_
    stack_mapped := ?_
    output_return := ?_
    output_stack := ?_
    header_bound := owned.header_bound
    address_load := ?_
    capacity_load := ?_
    used_load := ?_
    arena_bound := owned.arena_bound
    arena_nonzero := owned.arena_nonzero
    arena_mapped := initial_mapped s length ra _ _ owned.arena_mapped
    arena_output := ?_
    arena_stack := ?_
    arena_return := ?_
    arena_header := owned.arena_header
    header_output := ?_
    header_stack := ?_
    cursor_return := ?_ }
  · simp only [divisionReady, callState, NatDivision.callState, entryState, UInt64.toBitVec_ofBitVec]
  · simp only [divisionReady, callState, NatDivision.callState, entryState, UInt64.toBitVec_ofBitVec]
  · rfl
  · cases length with
    | small limb => trivial
    | large p limbs =>
      have hp := owned.operand_owned
      change Protected s address capacity used p.toNat (8 * limbs.length) at hp
      have apart := hp.work
      refine ⟨hp.bound, ?_, ?_, hp.cursor, hp.arena⟩
      · change Body.Apart p.toNat (8 * limbs.length) t.regs.rdi.toNat 68
        rw [outNat]
        simp only [Body.Apart, workStart, workSize] at apart ⊢
        omega
      · change Body.Apart p.toNat (8 * limbs.length) (t.regs.rsp.toNat - 64) 64
        rw [stackNat]
        simp only [Body.Apart, workStart, workSize] at apart ⊢
        omega
  · change t.regs.rdi.toNat + 68 ≤ 2^64
    rw [outNat]
    omega
  · change Large.Mapped t.dmem t.regs.rdi.toBitVec 68
    rw [out]
    have h := mapped_subrange t.dmem (s.regs.rsp.toBitVec - 72#64) workSize 88 68 workMapped (by decide)
    simpa only [show s.regs.rsp.toBitVec - 72#64 + BitVec.ofNat 64 88 =
      s.regs.rsp.toBitVec + 16#64 by bv_omega] using h
  · change t.regs.rsp.toNat + 8 ≤ 2^64
    rw [stackNat]
    omega
  · exact NatDivision.call_slot_load (entryMem s) (s.regs.rsp.toBitVec - 8#64) ra
  · change 64 ≤ t.regs.rsp.toNat
    rw [stackNat]
    omega
  · change Large.Mapped t.dmem (t.regs.rsp.toBitVec - 64#64) 64
    rw [stack, show s.regs.rsp.toBitVec - 8#64 - 64#64 = s.regs.rsp.toBitVec - 72#64 by bv_omega]
    exact fun i hi => workMapped i (by unfold workSize; omega)
  · change Body.Apart t.regs.rdi.toNat 68 t.regs.rsp.toNat 8
    rw [outNat, stackNat]
    unfold Body.Apart
    omega
  · change Body.Apart t.regs.rdi.toNat 68 (t.regs.rsp.toNat - 64) 64
    rw [outNat, stackNat]
    unfold Body.Apart
    omega
  · have h0 := headerRead 0 (by decide)
    simp only [BitVec.add_zero] at h0
    exact h0.trans owned.address_load
  · exact (headerRead 8 (by decide)).trans owned.capacity_load
  · exact (headerRead 16 (by decide)).trans owned.used_load
  · change Body.Apart _ _ t.regs.rdi.toNat 68
    rw [outNat]
    simp only [Body.Apart, workStart, workSize] at arenaWork ⊢
    omega
  · change Body.Apart _ _ (t.regs.rsp.toNat - 64) 64
    rw [stackNat]
    simp only [Body.Apart, workStart, workSize] at arenaWork ⊢
    omega
  · change Body.Apart _ _ t.regs.rsp.toNat 8
    rw [stackNat]
    simp only [Body.Apart, workStart, workSize] at arenaWork ⊢
    omega
  · change Body.Apart s.regs.rbx.toNat 24 t.regs.rdi.toNat 68
    rw [outNat]
    simp only [Body.Apart, workStart, workSize] at headerWork ⊢
    omega
  · change Body.Apart s.regs.rbx.toNat 24 (t.regs.rsp.toNat - 64) 64
    rw [stackNat]
    simp only [Body.Apart, workStart, workSize] at headerWork ⊢
    omega
  · change Body.Apart (s.regs.rbx.toNat + 16) 8 t.regs.rsp.toNat 8
    rw [stackNat]
    simp only [Body.Apart, workStart, workSize] at headerWork ⊢
    omega

end SszX86.BitVector

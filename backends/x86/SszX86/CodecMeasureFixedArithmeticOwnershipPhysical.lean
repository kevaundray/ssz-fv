import SszX86.CodecMeasureFixedArithmeticOwnershipMemory

namespace SszX86.CodecMeasureFixed
open SszNative UintCodec

/-- Shared physical regions at the deterministic pushed CALL cut. Provider-specific
register and operand contracts are assembled separately. -/
structure ArithmeticPhysical (m : DataMem) (out sp header : BitVec 64) (helper : Nat)
    (address capacity used ra : BitVec 64) : Prop where
  output_bound : out.toNat + 72 ≤ 2 ^ 64
  output_mapped : Large.Mapped m out 72
  return_bound : sp.toNat + 8 ≤ 2 ^ 64
  return_load : Mem.loadInt m sp 8 = some (Int.ofBytes (wordBytes ra))
  stack_low : helper ≤ sp.toNat
  stack_mapped : Large.Mapped m (sp - BitVec.ofNat 64 helper) helper
  output_return : Body.Apart out.toNat 72 sp.toNat 8
  output_stack : Body.Apart out.toNat 72 (sp.toNat - helper) helper
  header_bound : header.toNat + 24 ≤ 2 ^ 64
  address_load : Mem.loadInt m header 8 = some (address.toNat : Int)
  capacity_load : Mem.loadInt m (header + 8) 8 = some (capacity.toNat : Int)
  used_load : Mem.loadInt m (header + 16) 8 = some (used.toNat : Int)
  arena_bound : address.toNat + capacity.toNat ≤ 2 ^ 64
  used_bound : used.toNat ≤ capacity.toNat
  arena_nonzero : 0 < capacity.toNat → 0 < address.toNat
  arena_mapped : Large.Mapped m address capacity.toNat
  arena_output : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat) out.toNat 72
  arena_stack : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    (sp.toNat - helper) helper
  arena_return : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat) sp.toNat 8
  arena_header : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat) header.toNat 24
  header_output : Body.Apart header.toNat 24 out.toNat 72
  header_stack : Body.Apart header.toNat 24 (sp.toNat - helper) helper
  cursor_return : Body.Apart (header.toNat + 16) 8 sp.toNat 8

theorem arithmetic_physical (original caller : MachineData) (base : Int64) (r : Codec.Footprint)
    (desc : SszNative.Codec.Desc) (address capacity used originalRa ra : BitVec 64)
    (bytes helper : Nat) (owned : Owned original base r desc address capacity used originalRa bytes)
    (memory : caller.dmem = original.dmem)
    (stack : caller.regs.rsp.toBitVec = original.regs.rsp.toBitVec - 136)
    (enough : 144 + helper ≤ bytes) :
    ArithmeticCallSlot caller ∧
      ArithmeticPhysical (arithmeticCallState caller ra).dmem caller.regs.rsp.toBitVec
        (caller.regs.rsp.toBitVec - 8) original.regs.rdx.toBitVec helper address capacity used ra := by
  have low := owned.stack.lowEnough
  have originalBound := owned.return_bound
  have callerNat : caller.regs.rsp.toNat = original.regs.rsp.toNat - 136 := by
    have := congrArg BitVec.toNat stack
    simp only [BitVec.toNat_sub, UInt64.toNat_toBitVec] at this
    omega
  have pushedNat : (caller.regs.rsp.toBitVec - 8).toNat = original.regs.rsp.toNat - 144 := by
    simp only [BitVec.toNat_sub, UInt64.toNat_toBitVec]
    omega
  have outputMap := owned.stack.substack 64 72 (by omega)
  have outputPointer : original.regs.rsp.toBitVec - BitVec.ofNat 64 64 - BitVec.ofNat 64 72 =
      caller.regs.rsp.toBitVec := by rw [stack]; bv_omega
  have slotMap := owned.stack.substack 136 8 (by omega)
  have slotPointer : original.regs.rsp.toBitVec - BitVec.ofNat 64 136 - BitVec.ofNat 64 8 =
      caller.regs.rsp.toBitVec - 8 := by rw [stack]
  have helperMap := owned.stack.substack 144 helper enough
  have helperPointer : original.regs.rsp.toBitVec - BitVec.ofNat 64 144 - BitVec.ofNat 64 helper =
      caller.regs.rsp.toBitVec - 8 - BitVec.ofNat 64 helper := by rw [stack]; bv_omega
  have outputMapped : Large.Mapped original.dmem caller.regs.rsp.toBitVec 72 := by
    simpa only [outputPointer] using outputMap.mapped
  have slotMapped : Large.Mapped original.dmem (caller.regs.rsp.toBitVec - 8) 8 := by
    simpa only [slotPointer] using slotMap.mapped
  have helperMapped : Large.Mapped original.dmem
      (caller.regs.rsp.toBitVec - 8 - BitVec.ofNat 64 helper) helper := by
    simpa only [helperPointer] using helperMap.mapped
  have headerSlot : Body.Apart original.regs.rdx.toNat 24
      (caller.regs.rsp.toBitVec - 8).toNat 8 := by
    apply arithmetic_apart_subspan owned.header_stack
    · rw [pushedNat]; omega
    · rw [pushedNat]; omega
  have headerLoad (offset : Nat) (within : offset + 8 ≤ 24) :
      Mem.loadInt (arithmeticCallState caller ra).dmem
        (original.regs.rdx.toBitVec + BitVec.ofNat 64 offset) 8 =
      Mem.loadInt original.dmem (original.regs.rdx.toBitVec + BitVec.ofNat 64 offset) 8 := by
    change Mem.loadInt (Mem.storeInt caller.dmem (caller.regs.rsp.toBitVec - 8) 8 ra.toInt) _ 8 = _
    rw [memory]
    apply BoolCodec.load_store_disjoint
    have offsetNat : (original.regs.rdx.toBitVec + BitVec.ofNat 64 offset).toNat =
        original.regs.rdx.toNat + offset := by
      have hb := owned.header_bound
      bv_omega
    apply Body.apart_bytes
    · rw [offsetNat]; have hb := owned.header_bound; omega
    · rw [pushedNat]; omega
    · rw [offsetNat]
      exact (arithmetic_apart_subspan headerSlot.symm (by omega) (by omega)).symm
  constructor
  · unfold ArithmeticCallSlot
    rw [memory]
    exact Delimited.mapped_load_zero slotMapped (by decide)
  · refine {
      output_bound := by rw [UInt64.toNat_toBitVec, callerNat]; omega
      output_mapped := ?_
      return_bound := by rw [pushedNat]; omega
      return_load := NatDivision.call_slot_load caller.dmem (caller.regs.rsp.toBitVec - 8) ra
      stack_low := by rw [pushedNat]; omega
      stack_mapped := ?_
      output_return := ?_
      output_stack := ?_
      header_bound := owned.header_bound
      address_load := ?_
      capacity_load := ?_
      used_load := ?_
      arena_bound := owned.arena_bound
      used_bound := owned.used_bound
      arena_nonzero := owned.arena_nonzero
      arena_mapped := ?_
      arena_output := ?_
      arena_stack := ?_
      arena_return := ?_
      arena_header := owned.arena_header
      header_output := ?_
      header_stack := ?_
      cursor_return := ?_ }
    · change Large.Mapped (Mem.storeInt caller.dmem _ 8 ra.toInt) _ 72
      apply Large.mapped_store
      simpa only [memory] using outputMapped
    · change Large.Mapped (Mem.storeInt caller.dmem _ 8 ra.toInt) _ helper
      apply Large.mapped_store
      simpa only [memory] using helperMapped
    · rw [UInt64.toNat_toBitVec, callerNat, pushedNat]
      unfold Body.Apart
      omega
    · rw [UInt64.toNat_toBitVec, callerNat, pushedNat]
      unfold Body.Apart
      omega
    · simpa only [BitVec.ofNat_zero, BitVec.add_zero] using
        (headerLoad 0 (by decide)).trans owned.address_load
    · exact (headerLoad 8 (by decide)).trans owned.capacity_load
    · exact (headerLoad 16 (by decide)).trans owned.used_load
    · change Large.Mapped (Mem.storeInt caller.dmem _ 8 ra.toInt) _ _
      apply Large.mapped_store
      simpa only [memory] using owned.arena_mapped
    · apply arithmetic_apart_subspan owned.arena_stack
      · rw [UInt64.toNat_toBitVec, callerNat]; omega
      · rw [UInt64.toNat_toBitVec, callerNat]; omega
    · apply arithmetic_apart_subspan owned.arena_stack
      · rw [pushedNat]; omega
      · rw [pushedNat]; omega
    · apply arithmetic_apart_subspan owned.arena_stack
      · rw [pushedNat]; omega
      · rw [pushedNat]; omega
    · apply arithmetic_apart_subspan owned.header_stack
      · rw [UInt64.toNat_toBitVec, callerNat]; omega
      · rw [UInt64.toNat_toBitVec, callerNat]; omega
    · apply arithmetic_apart_subspan owned.header_stack
      · rw [pushedNat]; omega
      · rw [pushedNat]; omega
    · exact (arithmetic_apart_subspan headerSlot.symm (by omega) (by omega)).symm

end SszX86.CodecMeasureFixed

import SszX86.NatMulMemoryStack

namespace SszX86.NatMul
open SszNative
open UintCodec

/-- Physical exclusions needed by the actual memset return and setup spill. -/
structure InitializationSeparation (original current : MachineData) (dst : BitVec 64)
    (bytes : Nat) : Prop where
  stack_cursor : Large.Disjoint current.regs.rsp.toBitVec (original.regs.r9.toBitVec+16#64) 40 8
  stack_buffer : Large.Disjoint current.regs.rsp.toBitVec dst 40 bytes
  cursor_buffer : Large.Disjoint (original.regs.r9.toBitVec+16#64) dst 8 bytes
  cursor_call : Large.Disjoint (original.regs.r9.toBitVec+16#64) (current.regs.rsp.toBitVec-8#64) 8 8
  output_buffer : Large.Disjoint original.regs.rdi.toBitVec dst 72 bytes
  output_call : Large.Disjoint original.regs.rdi.toBitVec (current.regs.rsp.toBitVec-8#64) 72 8
  output_stack : Large.Disjoint original.regs.rdi.toBitVec current.regs.rsp.toBitVec 72 40
  stack_call : Large.Disjoint current.regs.rsp.toBitVec (current.regs.rsp.toBitVec-8#64) 40 8

theorem initialization_separation (original current : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (owned : Owned original left right address capacity used ra)
    (stack : current.regs.rsp.toBitVec = original.regs.rsp.toBitVec-88)
    (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).allocation = some r)
    (bytes : Nat)
    (size : 8*(SszNative.NatMul.run left right address.toNat capacity.toNat used.toNat).written.length = bytes) :
    InitializationSeparation original current (BitVec.ofNat 64 r.pointer) bytes := by
  have low := owned.stack_low
  change 96 ≤ original.regs.rsp.toBitVec.toNat at low
  have spBound := original.regs.rsp.toBitVec.isLt
  have outBound := owned.output_bound
  change original.regs.rdi.toBitVec.toNat+72 ≤ 2^64 at outBound
  have headerBound := owned.header_bound
  change original.regs.r9.toBitVec.toNat+24 ≤ 2^64 at headerBound
  have spNat : current.regs.rsp.toBitVec.toNat = original.regs.rsp.toBitVec.toNat-88 := by
    rw [stack]
    bv_omega
  have slotNat : (current.regs.rsp.toBitVec-8#64).toNat = original.regs.rsp.toBitVec.toNat-96 := by
    rw [stack]
    bv_omega
  have cursorNat : (original.regs.r9.toBitVec+16#64).toNat = original.regs.r9.toBitVec.toNat+16 := by
    bv_omega
  have pointerNat := allocated_pointer_nat original left right address capacity used ra owned r allocated
  have bounds := allocation_bounds original left right address capacity used ra owned r allocated
  rw [size] at bounds
  have stackBound : current.regs.rsp.toBitVec.toNat+40 ≤ 2^64 := by rw [spNat]; omega
  have slotBound : (current.regs.rsp.toBitVec-8#64).toNat+8 ≤ 2^64 := by rw [slotNat]; omega
  have cursorBound : (original.regs.r9.toBitVec+16#64).toNat+8 ≤ 2^64 := by rw [cursorNat]; omega
  have bufferBound : (BitVec.ofNat 64 r.pointer).toNat+bytes ≤ 2^64 := by
    rw [pointerNat]
    exact bounds.2.2.2.2.2
  have usedBound := owned.used_bound
  have arenaStack := owned.arena_stack
  change Body.Apart (address.toNat+used.toNat) (capacity.toNat-used.toNat)
    (original.regs.rsp.toBitVec.toNat-96) 96 at arenaStack
  have headerStack := owned.header_stack
  change Body.Apart original.regs.r9.toBitVec.toNat 24
    (original.regs.rsp.toBitVec.toNat-96) 96 at headerStack
  have outputStack := owned.output_stack
  change Body.Apart original.regs.rdi.toBitVec.toNat 72
    (original.regs.rsp.toBitVec.toNat-96) 96 at outputStack
  have arenaOutput := owned.arena_output
  change Body.Apart (address.toNat+used.toNat) (capacity.toNat-used.toNat)
    original.regs.rdi.toBitVec.toNat 72 at arenaOutput
  have arenaHeader := owned.arena_header
  change Body.Apart (address.toNat+used.toNat) (capacity.toNat-used.toNat)
    original.regs.r9.toBitVec.toNat 24 at arenaHeader
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Body.apart_bytes _ _ _ _ stackBound cursorBound
    rw [spNat, cursorNat]
    unfold Body.Apart at *
    omega
  · apply Body.apart_bytes _ _ _ _ stackBound bufferBound
    rw [spNat, pointerNat]
    unfold Body.Apart at *
    omega
  · apply Body.apart_bytes _ _ _ _ cursorBound bufferBound
    rw [cursorNat, pointerNat]
    unfold Body.Apart at *
    omega
  · apply Body.apart_bytes _ _ _ _ cursorBound slotBound
    rw [cursorNat, slotNat]
    unfold Body.Apart at *
    omega
  · apply Body.apart_bytes _ _ _ _ outBound bufferBound
    rw [pointerNat]
    unfold Body.Apart at *
    omega
  · apply Body.apart_bytes _ _ _ _ outBound slotBound
    rw [slotNat]
    unfold Body.Apart at *
    omega
  · apply Body.apart_bytes _ _ _ _ outBound stackBound
    rw [spNat]
    unfold Body.Apart at *
    omega
  · apply Body.apart_bytes _ _ _ _ stackBound slotBound
    rw [spNat, slotNat]
    unfold Body.Apart
    omega

end SszX86.NatMul

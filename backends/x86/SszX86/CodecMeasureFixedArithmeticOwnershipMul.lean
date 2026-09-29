import SszX86.CodecMeasureFixedArithmeticOwnershipOperands

namespace SszX86.CodecMeasureFixed
open SszNative UintCodec

theorem arithmetic_mul_owned (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64)
    (physical : ArithmeticPhysical s.dmem s.regs.rdi.toBitVec s.regs.rsp.toBitVec
      s.regs.r9.toBitVec 96 address capacity used ra)
    (leftPointer : s.regs.rsi.toBitVec = left.pointer)
    (leftPayload : s.regs.rdx.toBitVec = left.payload)
    (rightPointer : s.regs.rcx.toBitVec = right.pointer)
    (rightPayload : s.regs.r8.toBitVec = right.payload)
    (leftAt : left.At (widthLoad s.dmem)) (rightAt : right.At (widthLoad s.dmem))
    (leftSafe : ArithmeticOperandProtected s.regs.rdi.toBitVec s.regs.rsp.toBitVec
      s.regs.r9.toBitVec 96 address capacity used left)
    (rightSafe : ArithmeticOperandProtected s.regs.rdi.toBitVec s.regs.rsp.toBitVec
      s.regs.r9.toBitVec 96 address capacity used right) :
    NatMul.Owned s left right address capacity used ra := by
  have protect (operand : NatOperand)
      (safe : ArithmeticOperandProtected s.regs.rdi.toBitVec s.regs.rsp.toBitVec
        s.regs.r9.toBitVec 96 address capacity used operand) :
      NatMul.OperandProtected s address capacity used operand := by
    cases operand with
    | small word => trivial
    | large pointer words => exact ⟨safe.bound, safe.output, safe.activation, safe.cursor, safe.arena⟩
  have freeMapped : Large.Mapped s.dmem (address + used) (capacity.toNat - used.toNat) := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      Delimited.Reservation.mapped_subrange s.dmem address capacity.toNat used.toNat
        (capacity.toNat - used.toNat) physical.arena_mapped (by have := physical.used_bound; omega)
  exact {
    left_pointer := leftPointer
    left_payload := leftPayload
    right_pointer := rightPointer
    right_payload := rightPayload
    left_at := leftAt
    right_at := rightAt
    left_owned := protect left leftSafe
    right_owned := protect right rightSafe
    output_bound := physical.output_bound
    output_mapped := physical.output_mapped
    return_bound := physical.return_bound
    return_load := physical.return_load
    stack_low := physical.stack_low
    stack_mapped := physical.stack_mapped
    output_return := physical.output_return
    output_stack := physical.output_stack
    header_bound := physical.header_bound
    address_load := physical.address_load
    capacity_load := physical.capacity_load
    used_load := physical.used_load
    arena_bound := physical.arena_bound
    used_bound := physical.used_bound
    arena_nonzero := physical.arena_nonzero
    free_mapped := freeMapped
    arena_output := physical.arena_output
    arena_stack := physical.arena_stack
    arena_return := physical.arena_return
    arena_header := physical.arena_header
    header_output := physical.header_output
    header_stack := physical.header_stack
    cursor_return := physical.cursor_return }

theorem arithmetic_mul_owned_from_original (original caller : MachineData)
    (base : Int64) (r : Codec.Footprint) (desc : SszNative.Codec.Desc)
    (address capacity used originalRa ra : BitVec 64) (bytes : Nat)
    (owned : Owned original base r desc address capacity used originalRa bytes)
    (memory : caller.dmem = original.dmem)
    (stack : caller.regs.rsp.toBitVec = original.regs.rsp.toBitVec - 136)
    (output : caller.regs.rdi.toBitVec = caller.regs.rsp.toBitVec)
    (header : caller.regs.r9.toBitVec = original.regs.rdx.toBitVec)
    (enough : 240 ≤ bytes) (left right : NatOperand)
    (leftPointer : caller.regs.rsi.toBitVec = left.pointer)
    (leftPayload : caller.regs.rdx.toBitVec = left.payload)
    (rightPointer : caller.regs.rcx.toBitVec = right.pointer)
    (rightPayload : caller.regs.r8.toBitVec = right.payload)
    (leftAt : left.At (widthLoad original.dmem)) (rightAt : right.At (widthLoad original.dmem))
    (leftSafe : ArithmeticOperandSafe original bytes address capacity used left)
    (rightSafe : ArithmeticOperandSafe original bytes address capacity used right) :
    ArithmeticCallSlot caller ∧
      NatMul.Owned (arithmeticCallState caller ra) left right address capacity used ra := by
  obtain ⟨slot, physical⟩ := arithmetic_physical original caller base r desc address capacity used
    originalRa ra bytes 96 owned memory stack enough
  refine ⟨slot, arithmetic_mul_owned (arithmeticCallState caller ra) left right address capacity used ra
    ?_ leftPointer leftPayload rightPointer rightPayload ?_ ?_ ?_ ?_⟩
  · simpa only [arithmeticCallState, NatDivision.callState, UInt64.toBitVec_ofBitVec, output, header] using physical
  · exact arithmetic_operand_after_call original caller ra bytes address capacity used left memory stack
      (by omega) leftAt leftSafe
  · exact arithmetic_operand_after_call original caller ra bytes address capacity used right memory stack
      (by omega) rightAt rightSafe
  · simpa only [arithmeticCallState, NatDivision.callState, UInt64.toBitVec_ofBitVec, output, header] using
      arithmetic_operand_protected original caller base r desc address capacity used originalRa bytes 96
        owned stack enough left leftAt leftSafe
  · simpa only [arithmeticCallState, NatDivision.callState, UInt64.toBitVec_ofBitVec, output, header] using
      arithmetic_operand_protected original caller base r desc address capacity used originalRa bytes 96
        owned stack enough right rightAt rightSafe

end SszX86.CodecMeasureFixed

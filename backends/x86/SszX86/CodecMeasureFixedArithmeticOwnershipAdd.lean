import SszX86.CodecMeasureFixedArithmeticOwnershipOperands

namespace SszX86.CodecMeasureFixed
open SszNative UintCodec

theorem arithmetic_add_owned (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64)
    (physical : ArithmeticPhysical s.dmem s.regs.rdi.toBitVec s.regs.rsp.toBitVec
      s.regs.r9.toBitVec 48 address capacity used ra)
    (leftPointer : s.regs.rsi.toBitVec = left.pointer)
    (leftPayload : s.regs.rdx.toBitVec = left.payload)
    (rightPointer : s.regs.rcx.toBitVec = right.pointer)
    (rightPayload : s.regs.r8.toBitVec = right.payload)
    (leftAt : left.At (widthLoad s.dmem)) (rightAt : right.At (widthLoad s.dmem))
    (leftSafe : ArithmeticOperandProtected s.regs.rdi.toBitVec s.regs.rsp.toBitVec
      s.regs.r9.toBitVec 48 address capacity used left)
    (rightSafe : ArithmeticOperandProtected s.regs.rdi.toBitVec s.regs.rsp.toBitVec
      s.regs.r9.toBitVec 48 address capacity used right) :
    NatAdd.Owned s left right address capacity used ra := by
  have protect (operand : NatOperand)
      (safe : ArithmeticOperandProtected s.regs.rdi.toBitVec s.regs.rsp.toBitVec
        s.regs.r9.toBitVec 48 address capacity used operand) :
      NatAdd.OperandProtected s address capacity used operand := by
    cases operand with
    | small word => trivial
    | large pointer words =>
      exact ⟨safe.bound, arithmetic_apart_subspan safe.output (Nat.le_refl _) (by omega),
        safe.activation, safe.cursor, safe.arena⟩
  exact {
    left_pointer := leftPointer
    left_payload := leftPayload
    right_pointer := rightPointer
    right_payload := rightPayload
    left_at := leftAt
    right_at := rightAt
    left_owned := protect left leftSafe
    right_owned := protect right rightSafe
    output_bound := by have := physical.output_bound; omega
    output_mapped := fun i hi => physical.output_mapped i (by omega)
    return_bound := physical.return_bound
    return_load := physical.return_load
    stack_low := physical.stack_low
    stack_mapped := physical.stack_mapped
    output_return := (arithmetic_apart_subspan physical.output_return.symm (Nat.le_refl _) (by omega)).symm
    output_stack := (arithmetic_apart_subspan physical.output_stack.symm (Nat.le_refl _) (by omega)).symm
    header_bound := physical.header_bound
    address_load := physical.address_load
    capacity_load := physical.capacity_load
    used_load := physical.used_load
    arena_bound := physical.arena_bound
    used_bound := physical.used_bound
    arena_nonzero := physical.arena_nonzero
    arena_mapped := physical.arena_mapped
    arena_output := arithmetic_apart_subspan physical.arena_output (Nat.le_refl _) (by omega)
    arena_stack := physical.arena_stack
    arena_return := physical.arena_return
    arena_header := physical.arena_header
    header_output := arithmetic_apart_subspan physical.header_output (Nat.le_refl _) (by omega)
    header_stack := physical.header_stack
    cursor_return := physical.cursor_return }

/-- Genuine provider ownership follows from original-cut codec ownership and
current operand safety, with the CALL slot itself derived from the caller stack. -/
theorem arithmetic_add_owned_from_original (original caller : MachineData)
    (base : Int64) (r : Codec.Footprint) (desc : SszNative.Codec.Desc)
    (address capacity used originalRa ra : BitVec 64) (bytes : Nat)
    (owned : Owned original base r desc address capacity used originalRa bytes)
    (memory : caller.dmem = original.dmem)
    (stack : caller.regs.rsp.toBitVec = original.regs.rsp.toBitVec - 136)
    (output : caller.regs.rdi.toBitVec = caller.regs.rsp.toBitVec)
    (header : caller.regs.r9.toBitVec = original.regs.rdx.toBitVec)
    (enough : 192 ≤ bytes) (left right : NatOperand)
    (leftPointer : caller.regs.rsi.toBitVec = left.pointer)
    (leftPayload : caller.regs.rdx.toBitVec = left.payload)
    (rightPointer : caller.regs.rcx.toBitVec = right.pointer)
    (rightPayload : caller.regs.r8.toBitVec = right.payload)
    (leftAt : left.At (widthLoad original.dmem)) (rightAt : right.At (widthLoad original.dmem))
    (leftSafe : ArithmeticOperandSafe original bytes address capacity used left)
    (rightSafe : ArithmeticOperandSafe original bytes address capacity used right) :
    ArithmeticCallSlot caller ∧
      NatAdd.Owned (arithmeticCallState caller ra) left right address capacity used ra := by
  obtain ⟨slot, physical⟩ := arithmetic_physical original caller base r desc address capacity used
    originalRa ra bytes 48 owned memory stack enough
  refine ⟨slot, arithmetic_add_owned (arithmeticCallState caller ra) left right address capacity used ra
    ?_ leftPointer leftPayload rightPointer rightPayload ?_ ?_ ?_ ?_⟩
  · simpa only [arithmeticCallState, NatDivision.callState, UInt64.toBitVec_ofBitVec, output, header] using physical
  · exact arithmetic_operand_after_call original caller ra bytes address capacity used left memory stack
      (by omega) leftAt leftSafe
  · exact arithmetic_operand_after_call original caller ra bytes address capacity used right memory stack
      (by omega) rightAt rightSafe
  · simpa only [arithmeticCallState, NatDivision.callState, UInt64.toBitVec_ofBitVec, output, header] using
      arithmetic_operand_protected original caller base r desc address capacity used originalRa bytes 48
        owned stack enough left leftAt leftSafe
  · simpa only [arithmeticCallState, NatDivision.callState, UInt64.toBitVec_ofBitVec, output, header] using
      arithmetic_operand_protected original caller base r desc address capacity used originalRa bytes 48
        owned stack enough right rightAt rightSafe

end SszX86.CodecMeasureFixed

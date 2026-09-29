import SszX86.CodecMeasureFixedArithmeticOwnershipOperands

namespace SszX86.CodecMeasureFixed
open SszNative UintCodec

theorem arithmetic_divide8_owned (s : MachineData) (operand : NatOperand)
    (address capacity used ra : BitVec 64)
    (physical : ArithmeticPhysical s.dmem s.regs.rdi.toBitVec s.regs.rsp.toBitVec
      s.regs.r8.toBitVec 64 address capacity used ra)
    (pointer : s.regs.rsi.toBitVec = operand.pointer)
    (payload : s.regs.rdx.toBitVec = operand.payload)
    (divisor : s.regs.rcx.toBitVec = 8)
    (stored : operand.At (widthLoad s.dmem))
    (safe : ArithmeticOperandProtected s.regs.rdi.toBitVec s.regs.rsp.toBitVec
      s.regs.r8.toBitVec 64 address capacity used operand) :
    NatDivision.Owned s operand 8 address capacity used ra := by
  have protect : NatDivision.OperandProtected s address capacity used operand := by
    cases operand with
    | small word => trivial
    | large pointer words =>
      exact ⟨safe.bound, arithmetic_apart_subspan safe.output (Nat.le_refl _) (by omega),
        safe.activation, safe.cursor, safe.arena⟩
  exact {
    operand_pointer := pointer
    operand_payload := payload
    divisor_register := divisor
    divisor_lower := by decide
    operand_at := stored
    operand_owned := protect
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
    arena_nonzero := physical.arena_nonzero
    arena_mapped := physical.arena_mapped
    arena_output := arithmetic_apart_subspan physical.arena_output (Nat.le_refl _) (by omega)
    arena_stack := physical.arena_stack
    arena_return := physical.arena_return
    arena_header := physical.arena_header
    header_output := arithmetic_apart_subspan physical.header_output (Nat.le_refl _) (by omega)
    header_stack := physical.header_stack
    cursor_return := physical.cursor_return }

theorem arithmetic_divide8_owned_from_original (original caller : MachineData)
    (base : Int64) (r : Codec.Footprint) (desc : SszNative.Codec.Desc)
    (address capacity used originalRa ra : BitVec 64) (bytes : Nat)
    (owned : Owned original base r desc address capacity used originalRa bytes)
    (memory : caller.dmem = original.dmem)
    (stack : caller.regs.rsp.toBitVec = original.regs.rsp.toBitVec - 136)
    (output : caller.regs.rdi.toBitVec = caller.regs.rsp.toBitVec)
    (header : caller.regs.r8.toBitVec = original.regs.rdx.toBitVec)
    (enough : 208 ≤ bytes) (operand : NatOperand)
    (pointer : caller.regs.rsi.toBitVec = operand.pointer)
    (payload : caller.regs.rdx.toBitVec = operand.payload)
    (divisor : caller.regs.rcx.toBitVec = 8)
    (stored : operand.At (widthLoad original.dmem))
    (safe : ArithmeticOperandSafe original bytes address capacity used operand) :
    ArithmeticCallSlot caller ∧
      NatDivision.Owned (arithmeticCallState caller ra) operand 8 address capacity used ra := by
  obtain ⟨slot, physical⟩ := arithmetic_physical original caller base r desc address capacity used
    originalRa ra bytes 64 owned memory stack enough
  refine ⟨slot, arithmetic_divide8_owned (arithmeticCallState caller ra) operand address capacity used ra
    ?_ pointer payload divisor ?_ ?_⟩
  · simpa only [arithmeticCallState, NatDivision.callState, UInt64.toBitVec_ofBitVec, output, header] using physical
  · exact arithmetic_operand_after_call original caller ra bytes address capacity used operand memory stack
      (by omega) stored safe
  · simpa only [arithmeticCallState, NatDivision.callState, UInt64.toBitVec_ofBitVec, output, header] using
      arithmetic_operand_protected original caller base r desc address capacity used originalRa bytes 64
        owned stack enough operand stored safe

end SszX86.CodecMeasureFixed

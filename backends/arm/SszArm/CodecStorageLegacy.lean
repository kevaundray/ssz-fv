import SszArm.CodecStorageChildren

namespace SszArm.Codec.Storage

open SszNative (NatOperand)
open SszNative.Codec (Value)
open Delimited (Span Protected)

 theorem operand_owned {writes s address number}
    (input : (Image.operand address number).Owned writes s) :
    NatDivision.OperandOwned writes number := by
  cases number with
  | small word => trivial
  | large pointer words => exact input.2.2.1.2

 theorem descriptor_operands_owned {writes s address shape}
    (input : DescOwned writes s address (.primitive shape)) (number : NatOperand)
    (member : number ∈ Emit.descriptorOperands shape) :
    NatDivision.OperandOwned writes number := by
  cases shape with
  | bool => simp [Emit.descriptorOperands] at member
  | uint n | byteVector n | byteList n | bitVector n | bitList n =>
      simp only [Emit.descriptorOperands, List.mem_singleton] at member
      subst number
      exact operand_owned input.2.2
  | progressiveBitList limit =>
      cases limit with
      | none => simp [Emit.descriptorOperands] at member
      | some n =>
          simp only [Emit.descriptorOperands, List.mem_singleton] at member
          subst number
          exact operand_owned input.2.2.2

 theorem value_operands_owned {writes s address logical}
    (input : ValueOwned writes s address logical) (number : NatOperand)
    (member : number ∈ Emit.valueOperands logical.toPrimitive) :
    NatDivision.OperandOwned writes number := by
  cases logical with
  | uint n =>
      simp only [Value.toPrimitive, Emit.valueOperands, List.mem_singleton] at member
      subst number
      exact operand_owned input.2.2
  | _ => simp [Value.toPrimitive, Emit.valueOperands] at member

 theorem primitive_value_physical {s address logical} (input : ValueAt s address logical) :
    logical.toPrimitive.Physical := by
  cases logical with
  | bytes data =>
      obtain ⟨pointer, _, _, physical, _⟩ := input.2.2
      have bound := physical.2.2.2
      change data.size < 2^64
      simp only [Nat.mul_one] at bound
      omega
  | bits data =>
      obtain ⟨pointer, _, _, physical, _⟩ := input.2.2.1
      have bound := physical.2.2.2
      change data.bytes.size < 2^64
      simp only [Nat.mul_one] at bound
      omega
  | _ => trivial

 theorem descriptor_protected {writes s address shape}
    (input : DescOwned writes s address shape) : Protected writes address 40 := by
  cases shape <;> exact input.1.2

 theorem value_protected {writes s address logical}
    (input : ValueOwned writes s address logical) : Protected writes address 48 := by
  cases logical <;> exact input.1.2

 theorem value_backing_owned {writes s logical} (args : Emit.Args)
    (input : ValueOwned writes s args.value.toNat logical) :
    ∀ span ∈ Emit.backingSpan s args logical.toPrimitive,
      Protected writes span.1 span.2 := by
  intro span member
  cases logical with
  | bytes data =>
      simp only [Value.toPrimitive, Emit.backingSpan, List.mem_singleton] at member
      subst span
      obtain ⟨pointer, pointerAt, _, _, bytesAt⟩ := input.2.2
      change Protected writes (read_mem_bytes 8 (args.value + 8#64) s).toNat data.size
      rw [word_offset args.value 8 pointerAt]
      exact bytesAt.2.1
  | bits data =>
      simp only [Value.toPrimitive, Emit.backingSpan, List.mem_singleton] at member
      subst span
      obtain ⟨pointer, pointerAt, _, _, bytesAt⟩ := input.2.2.1
      change Protected writes (read_mem_bytes 8 (args.value + 16#64) s).toNat data.bytes.size
      rw [word_offset args.value 16 pointerAt]
      exact bytesAt.2.1
  | _ => simp [Value.toPrimitive, Emit.backingSpan] at member

/-- Read-only premises of the legacy primitive emitter. Output, stack, expected
size and frame-budget premises remain with its execution caller. Physical record
protection includes padding; DescriptorAt/ValueAt still initialize no padding. -/
structure PrimitiveInputs (writes : List Span) (s : ArmState) (args : Emit.Args)
    (shape : SszNative.Serialize.Desc) (logical : Value) : Prop where
  physical : logical.toPrimitive.Physical
  descriptorBound : args.descriptor.toNat + Emit.descriptorBytes shape ≤ 2^64
  descriptor : Emit.DescriptorAt s args.descriptor shape
  valueBound : args.value.toNat + Emit.valueBytes logical.toPrimitive ≤ 2^64
  value_at : Emit.ValueAt s args.value logical.toPrimitive
  descriptorOwned : Protected writes args.descriptor.toNat (Emit.descriptorBytes shape)
  valueOwned : Protected writes args.value.toNat (Emit.valueBytes logical.toPrimitive)
  operandOwned : ∀ operand ∈ Emit.descriptorOperands shape ++ Emit.valueOperands logical.toPrimitive,
    NatDivision.OperandOwned writes operand
  backingOwned : ∀ span ∈ Emit.backingSpan s args logical.toPrimitive,
    Protected writes span.1 span.2

 theorem primitive_inputs {writes s args shape logical}
    (descriptor : DescOwned writes s args.descriptor.toNat (.primitive shape))
    (stored : ValueOwned writes s args.value.toNat logical) :
    PrimitiveInputs writes s args shape logical := by
  have descSize : Emit.descriptorBytes shape ≤ 40 := by
    cases shape <;> simp [Emit.descriptorBytes]
  have valueSize : Emit.valueBytes logical.toPrimitive ≤ 48 := by
    cases logical <;> simp [Value.toPrimitive, Emit.valueBytes]
  have descBound := (desc_physical (desc_at descriptor)).2.2.1
  have valueBound := (value_physical (value_at stored)).2.2.1
  refine ⟨primitive_value_physical (value_at stored), by omega,
    primitive_projection (desc_at descriptor), by omega, value_projection (value_at stored),
    ?_, ?_, ?_, value_backing_owned args stored⟩
  · simpa only [Nat.add_zero] using (descriptor_protected descriptor).subspan 0 _ descSize
  · simpa only [Nat.add_zero] using (value_protected stored).subspan 0 _ valueSize
  · intro operand member
    rcases List.mem_append.mp member with left | right
    · exact descriptor_operands_owned descriptor operand left
    · exact value_operands_owned stored operand right

end SszArm.Codec.Storage

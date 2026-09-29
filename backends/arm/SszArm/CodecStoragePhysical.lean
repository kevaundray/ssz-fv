import SszArm.CodecStorageLegacy

namespace SszArm.Codec.Storage

open SszNative (NatOperand)
open SszNative.Codec (Desc Value operandSliceSized optionalOperandSliceSized primitiveSliceSized)

 theorem word64_bound {protect s address number}
    (input : (Image.word address 8 number).Holds protect s) : number < 2^64 := by
  have bound := (read_mem_bytes 8 (BitVec.ofNat 64 address) s).isLt
  rw [word_read input] at bound
  exact bound

 theorem operand_sliceSized {protect s address number}
    (input : (Image.operand address number).Holds protect s) : operandSliceSized number := by
  cases number with
  | small word => trivial
  | large pointer words =>
      have bound := input.2.2.1.1
      change words.length < 2^64
      omega

 theorem optional_sliceSized {protect s address number}
    (input : (optionOperand address number).Holds protect s) : optionalOperandSliceSized number := by
  cases number with
  | none => trivial
  | some number => exact operand_sliceSized input.2

 theorem primitive_sliceSized {protect s address shape}
    (input : (primitive address shape).Holds protect s) : primitiveSliceSized shape := by
  cases shape with
  | bool => trivial
  | uint n | byteVector n | byteList n | bitVector n | bitList n =>
      exact operand_sliceSized input.2
  | progressiveBitList limit => exact optional_sliceSized input.2

mutual
  theorem desc_model_physical {protect s address} (shape : Desc)
      (input : (desc address shape).Holds protect s) : shape.Physical := by
    cases shape with
    | primitive shape => exact primitive_sliceSized input.2
    | vector child count =>
        obtain ⟨pointer, _, stored⟩ := vector_child input
        exact ⟨desc_model_physical child stored, operand_sliceSized input.2.2.1⟩
    | list child limit =>
        obtain ⟨pointer, _, stored⟩ := list_child input
        exact ⟨desc_model_physical child stored, operand_sliceSized input.2.2.1⟩
    | progressiveList child limit =>
        obtain ⟨pointer, _, stored⟩ := progressiveList_child input
        exact ⟨desc_model_physical child stored, optional_sliceSized input.2.2.1⟩
    | container fields =>
        obtain ⟨pointer, _, count, _, stored⟩ := container_fields input
        exact ⟨word64_bound count, fields_model_physical fields stored⟩
    | progressiveContainer active fields =>
        obtain ⟨activePointer, _, activeCount, _, _⟩ := input.2.2.1
        obtain ⟨pointer, _, count, _, stored⟩ := progressiveContainer_fields input
        exact ⟨word64_bound activeCount, word64_bound count, fields_model_physical fields stored⟩
    | compatibleUnion variants =>
        obtain ⟨pointer, _, count, _, stored⟩ := compatibleUnion_variants input
        exact ⟨word64_bound count, variants_model_physical variants stored⟩

  theorem fields_model_physical {protect s address} (fields : List (String × Desc))
      (input : (fieldEntries address fields).Holds protect s) : Desc.fieldsPhysical fields := by
    cases fields with
    | nil => trivial
    | cons field rest =>
        obtain ⟨name, shape⟩ := field
        obtain ⟨namePointer, _, length, _, _⟩ := input.1.2.1
        obtain ⟨pointer, _, stored⟩ := field_child input
        exact ⟨word64_bound length, desc_model_physical shape stored,
          fields_model_physical rest input.2⟩

  theorem variants_model_physical {protect s address} (variants : List (NatOperand × Desc))
      (input : (variantEntries address variants).Holds protect s) : Desc.variantsPhysical variants := by
    cases variants with
    | nil => trivial
    | cons variant rest =>
        obtain ⟨selector, shape⟩ := variant
        obtain ⟨pointer, _, stored⟩ := variant_child input
        exact ⟨operand_sliceSized input.1.2.1, desc_model_physical shape stored,
          variants_model_physical rest input.2⟩
end

mutual
  theorem value_model_physical {protect s address} (logical : Value)
      (input : (value address logical).Holds protect s) : logical.Physical := by
    cases logical with
    | bool flag => trivial
    | uint number => exact operand_sliceSized input.2.2
    | bytes data =>
        obtain ⟨pointer, _, length, _, _⟩ := input.2.2
        exact word64_bound length
    | bits data =>
        obtain ⟨pointer, _, length, _, _⟩ := input.2.2.1
        exact word64_bound length
    | seq children =>
        obtain ⟨pointer, _, count, _, stored⟩ := sequence_children input
        exact ⟨word64_bound count, values_model_physical children stored⟩
    | union selector child =>
        obtain ⟨pointer, _, stored⟩ := union_child input
        exact ⟨operand_sliceSized input.2.2.1, value_model_physical child stored⟩

  theorem values_model_physical {protect s address} (children : List Value)
      (input : (valueEntries address children).Holds protect s) : Value.listPhysical children := by
    cases children with
    | nil => trivial
    | cons child rest =>
        exact ⟨value_model_physical child input.1, values_model_physical rest input.2⟩
end

 theorem DescAt.physical {s address shape} (input : DescAt s address shape) : shape.Physical :=
  desc_model_physical shape input

 theorem ValueAt.physical {s address logical} (input : ValueAt s address logical) : logical.Physical :=
  value_model_physical logical input

end SszArm.Codec.Storage

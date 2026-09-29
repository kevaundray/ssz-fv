import SszArm.CodecStorageModels

namespace SszArm.Codec.Storage

open SszNative.Codec (Desc Value)
open SszNative.CodecMeasure (Plan)
open SszNative.CodecDecode (Node)
open UintCodec (widthLoad)

 theorem word_read {protect s address bytes number}
    (input : (Image.word address bytes number).Holds protect s) :
    (read_mem_bytes bytes (BitVec.ofNat 64 address) s).toNat = number :=
  Option.some.inj input.2.2

 theorem word_offset {protect s bytes number} (address : BitVec 64) (offset : Nat)
    (input : (Image.word (address.toNat + offset) bytes number).Holds protect s) :
    (read_mem_bytes bytes (address + BitVec.ofNat 64 offset) s).toNat = number := by
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using word_read input

 theorem word_bits {protect s address bytes} (bits : BitVec (bytes * 8))
    (input : (Image.word address bytes bits.toNat).Holds protect s) :
    read_mem_bytes bytes (BitVec.ofNat 64 address) s = bits :=
  BitVec.eq_of_toNat_eq (word_read input)

 theorem desc_physical {s address shape} (input : DescAt s address shape) :
    Physical address 40 8 := by
  cases shape <;> exact input.1.1

 theorem value_physical {s address logical} (input : ValueAt s address logical) :
    Physical address 48 16 := by
  cases logical <;> exact input.1.1

 theorem primitive_projection {s : ArmState} {address : BitVec 64}
    {shape : SszNative.Serialize.Desc} (input : DescAt s address.toNat (.primitive shape)) :
    Emit.DescriptorAt s address shape := by
  have tag : read_mem_bytes 8 address s = Emit.descriptorTag shape := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      word_bits (bytes := 8) (Emit.descriptorTag shape) input.2.1
  refine ⟨tag, ?_⟩
  cases shape with
  | bool => trivial
  | uint n | byteVector n | byteList n | bitVector n | bitList n =>
      exact input.2.2.2.2.2
  | progressiveBitList limit =>
      cases limit with
      | none =>
          apply BitVec.eq_of_toNat_eq
          exact word_offset address 8 input.2.2
      | some number =>
          refine ⟨?_, ?_⟩
          · apply BitVec.eq_of_toNat_eq
            exact word_offset address 8 input.2.2.1
          · simpa only [Nat.add_assoc] using input.2.2.2.2.2.2

 theorem value_projection {s : ArmState} {address : BitVec 64} {logical : Value}
    (input : ValueAt s address.toNat logical) :
    Emit.ValueAt s address logical.toPrimitive := by
  cases logical with
  | bool flag =>
      refine ⟨?_, ?_⟩
      · simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, Value.toPrimitive, Emit.valueTag] using
          word_bits (bytes := 1) (0 : BitVec (1 * 8)) input.2.1
      · apply BitVec.eq_of_toNat_eq
        cases flag <;> exact word_offset address 1 input.2.2
  | uint number =>
      refine ⟨?_, input.2.2.2.2.2⟩
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, Value.toPrimitive, Emit.valueTag] using
        word_bits (bytes := 1) (1 : BitVec (1 * 8)) input.2.1
  | bytes data =>
      refine ⟨?_, ?_⟩
      · simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, Value.toPrimitive, Emit.valueTag] using
          word_bits (bytes := 1) (2 : BitVec (1 * 8)) input.2.1
      · obtain ⟨pointer, pointerAt, lengthAt, physical, bytesAt⟩ := input.2.2
        have pointerRead := word_offset address 8 pointerAt
        have lengthRead := word_offset address 16 (by
          simpa only [Nat.add_assoc] using lengthAt)
        exact ⟨lengthRead, by rw [pointerRead]; exact bytesAt.1,
          by rw [pointerRead]; exact bytesAt.2.2⟩
  | bits data =>
      refine ⟨?_, ?_⟩
      · simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, Value.toPrimitive, Emit.valueTag] using
          word_bits (bytes := 1) (3 : BitVec (1 * 8)) input.2.1
      · obtain ⟨pointer, pointerAt, lengthAt, physical, bytesAt⟩ := input.2.2.1
        have pointerRead := word_offset address 16 pointerAt
        have lengthRead := word_offset address 24 (by
          simpa only [Nat.add_assoc] using lengthAt)
        refine ⟨lengthRead, ?_, ?_, ?_, ?_⟩
        · rw [pointerRead]; exact bytesAt.1
        · rw [pointerRead]; exact bytesAt.2.2
        · exact BitVec.eq_of_toNat_eq (word_offset address 32 input.2.2.2.1)
        · exact BitVec.eq_of_toNat_eq (word_offset address 40 input.2.2.2.2)
  | seq children =>
      refine ⟨?_, True.intro⟩
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, Value.toPrimitive, Emit.valueTag] using
        word_bits (bytes := 1) (4 : BitVec (1 * 8)) input.2.1
  | union selector child =>
      refine ⟨?_, True.intro⟩
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, Value.toPrimitive, Emit.valueTag] using
        word_bits (bytes := 1) (5 : BitVec (1 * 8)) input.2.1

 theorem plan_fields {s address logical} (input : PlanAt s address logical) :
    SszNative.CodecMeasure.PlanFields (widthLoad s) address logical := by
  cases logical with
  | mk size leading children allocation =>
      exact ⟨input.2.1.2.2, input.2.2.1.2.2,
        input.2.2.2.1.2.2.2.1, input.2.2.2.1.2.2.2.2.1,
        input.2.2.2.2.1.2.2⟩

end SszArm.Codec.Storage

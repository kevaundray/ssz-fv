import SszArm.EmitMemory

namespace SszArm.Emit

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value)
open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame)

theorem descriptor_operand_at {s : ArmState} {address : BitVec 64} {desc : Desc}
    (input : DescriptorAt s address desc) (operand : NatOperand)
    (member : operand ∈ descriptorOperands desc) : operand.At (widthLoad s) := by
  cases desc with
  | bool => simp [descriptorOperands] at member
  | uint width | byteVector width | byteList width | bitVector width | bitList width =>
    simp only [descriptorOperands, List.mem_singleton] at member
    subst operand
    exact input.2.2.2
  | progressiveBitList limit =>
    cases limit with
    | none => simp [descriptorOperands] at member
    | some width =>
      simp only [descriptorOperands, List.mem_singleton] at member
      subst operand
      exact input.2.2.2.2

theorem value_operand_at {s : ArmState} {address : BitVec 64} {value : Value}
    (input : ValueAt s address value) (operand : NatOperand)
    (member : operand ∈ valueOperands value) : operand.At (widthLoad s) := by
  cases value with
  | uint number =>
    simp only [valueOperands, List.mem_singleton] at member
    subst operand
    exact input.2.2.2
  | _ => simp [valueOperands] at member

theorem Owned.operand_at {s : ArmState} {args : Args} {desc : Desc} {value : Value} {size : Nat}
    (owned : Owned s args desc value size) (operand : NatOperand)
    (member : operand ∈ descriptorOperands desc ++ valueOperands value) :
    operand.At (widthLoad s) := by
  rcases List.mem_append.mp member with descriptor | value
  · exact descriptor_operand_at owned.descriptor operand descriptor
  · exact value_operand_at owned.value_at operand value

theorem descriptor_preserved {s t : ArmState} {args : Args} {desc : Desc} {value : Value} {size : Nat}
    (owned : Owned s args desc value size) (frame : MemoryFrame (writesFor args size) s t) :
    DescriptorAt t args.descriptor desc := by
  have header : ∀ offset operand, offset + 16 ≤ descriptorBytes desc →
      operand ∈ descriptorOperands desc →
      SszNative.NatArithmetic.operandAt (widthLoad s) (args.descriptor.toNat + offset) operand →
      SszNative.NatArithmetic.operandAt (widthLoad t) (args.descriptor.toNat + offset) operand := by
    intro offset operand within member input
    apply operand_header_preserved frame _ operand
    · have bound := owned.descriptorBound
      omega
    · exact owned.descriptorOwned.subspan offset 16 within
    · exact owned.operandOwned operand (List.mem_append.mpr (Or.inl member))
    · exact input
  have tag : read_mem_bytes 8 args.descriptor t = descriptorTag desc := by
    have within : 0 + 8 ≤ descriptorBytes desc := by cases desc <;> simp [descriptorBytes]
    have unchanged := frame_read_offset frame args.descriptor (descriptorBytes desc) 0 8
      owned.descriptorBound owned.descriptorOwned within
    simp only [BitVec.add_zero] at unchanged
    exact unchanged.trans owned.descriptor.1
  refine ⟨tag, ?_⟩
  cases desc with
  | bool => trivial
  | uint operand | byteVector operand | byteList operand | bitVector operand | bitList operand =>
    exact header 8 operand (by simp [descriptorBytes]) (by simp [descriptorOperands]) owned.descriptor.2
  | progressiveBitList limit =>
    cases limit with
    | none =>
      exact (frame_read_offset frame args.descriptor 32 8 8 owned.descriptorBound
        owned.descriptorOwned (by decide)).trans owned.descriptor.2
    | some operand =>
      exact ⟨(frame_read_offset frame args.descriptor 32 8 8 owned.descriptorBound
        owned.descriptorOwned (by decide)).trans owned.descriptor.2.1,
        header 16 operand (by simp [descriptorBytes]) (by simp [descriptorOperands]) owned.descriptor.2.2⟩

theorem value_preserved {s t : ArmState} {args : Args} {desc : Desc} {value : Value} {size : Nat}
    (owned : Owned s args desc value size) (frame : MemoryFrame (writesFor args size) s t) :
    ValueAt t args.value value := by
  have tag : read_mem_bytes 1 args.value t = valueTag value := by
    have within : 0 + 1 ≤ valueBytes value := by cases value <;> simp [valueBytes]
    have unchanged := frame_read_offset frame args.value (valueBytes value) 0 1
      owned.valueBound owned.valueOwned within
    simp only [BitVec.add_zero] at unchanged
    exact unchanged.trans owned.value_at.1
  refine ⟨tag, ?_⟩
  cases value with
  | bool flag =>
    exact (frame_read_offset frame args.value 2 1 1 owned.valueBound owned.valueOwned (by decide)).trans
      owned.value_at.2
  | uint number =>
    apply operand_header_preserved frame _ number
    · have bound := owned.valueBound
      change args.value.toNat + 24 ≤ 2^64 at bound
      omega
    · exact owned.valueOwned.subspan 8 16 (by simp [valueBytes])
    · exact owned.operandOwned number (List.mem_append.mpr (Or.inr (by simp [valueOperands])))
    · exact owned.value_at.2
  | bytes data =>
    have r8 := frame_read_offset frame args.value 24 8 8 owned.valueBound owned.valueOwned (by decide)
    have r16 := frame_read_offset frame args.value 24 16 8 owned.valueBound owned.valueOwned (by decide)
    change (read_mem_bytes 8 (args.value + 16#64) t).toNat = data.size ∧ _
    rw [r16, r8]
    refine ⟨owned.value_at.2.1, owned.value_at.2.2.1, ?_⟩
    exact frame.bytes _ data owned.value_at.2.2.1
      (owned.backingOwned ((read_mem_bytes 8 (args.value + 8#64) s).toNat, data.size)
        (by simp [backingSpan])) owned.value_at.2.2.2
  | bits data =>
    have r16 := frame_read_offset frame args.value 48 16 8 owned.valueBound owned.valueOwned (by decide)
    have r24 := frame_read_offset frame args.value 48 24 8 owned.valueBound owned.valueOwned (by decide)
    have r32 := frame_read_offset frame args.value 48 32 8 owned.valueBound owned.valueOwned (by decide)
    have r40 := frame_read_offset frame args.value 48 40 8 owned.valueBound owned.valueOwned (by decide)
    change (read_mem_bytes 8 (args.value + 24#64) t).toNat = data.bytes.size ∧ _
    rw [r24, r16, r32, r40]
    refine ⟨owned.value_at.2.1, owned.value_at.2.2.1, ?_, owned.value_at.2.2.2.2⟩
    exact frame.bytes _ data.bytes owned.value_at.2.2.1
      (owned.backingOwned ((read_mem_bytes 8 (args.value + 16#64) s).toNat, data.bytes.size)
        (by simp [backingSpan])) owned.value_at.2.2.2.1
  | seq _ | union _ _ => trivial

theorem backing_preserved {s t : ArmState} {args : Args} {desc : Desc} {value : Value} {size : Nat}
    (owned : Owned s args desc value size) (frame : MemoryFrame (writesFor args size) s t) :
    backingSpan t args value = backingSpan s args value := by
  cases value with
  | bytes data =>
    have r8 := frame_read_offset frame args.value 24 8 8 owned.valueBound owned.valueOwned (by decide)
    simp only [backingSpan, r8]
  | bits data =>
    have r16 := frame_read_offset frame args.value 48 16 8 owned.valueBound owned.valueOwned (by decide)
    simp only [backingSpan, r16]
  | _ => rfl

theorem Owned.of_frame {s t : ArmState} {args : Args} {desc : Desc} {value : Value} {size : Nat}
    (owned : Owned s args desc value size) (frame : MemoryFrame (writesFor args size) s t) :
    Owned t args desc value size := by
  refine { owned with
    descriptor := descriptor_preserved owned frame
    value_at := value_preserved owned frame
    backingOwned := ?_ }
  simpa only [backing_preserved owned frame] using owned.backingOwned

end SszArm.Emit

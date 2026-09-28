import SszArm.SerializeGeometry

namespace SszArm.Serialize

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value)
open UintCodec (widthLoad)
open Delimited (MemoryFrame)

theorem Owned.operand_at {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (operand : NatOperand)
    (member : operand ∈ Emit.descriptorOperands desc ++ Emit.valueOperands value) :
    operand.At (widthLoad s) := by
  rcases List.mem_append.mp member with descriptor | input
  · exact Emit.descriptor_operand_at owned.descriptor operand descriptor
  · exact Emit.value_operand_at owned.value_at operand input

/-- Transport observes only the original live descriptor and its borrowed limbs. -/
theorem descriptor_preserved {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (frame : MemoryFrame (writable s args) s t) :
    Emit.DescriptorAt t args.descriptor desc := by
  have header : ∀ displacement operand, displacement + 16 ≤ Emit.descriptorBytes desc →
      operand ∈ Emit.descriptorOperands desc →
      SszNative.NatArithmetic.operandAt (widthLoad s) (args.descriptor.toNat + displacement) operand →
      SszNative.NatArithmetic.operandAt (widthLoad t) (args.descriptor.toNat + displacement) operand := by
    intro displacement operand within member input
    apply Emit.operand_header_preserved frame _ operand
    · have bound := owned.descriptorBound
      omega
    · exact owned.descriptorOwned.subspan displacement 16 within
    · exact owned.operandOwned operand (List.mem_append.mpr (Or.inl member))
    · exact input
  have tag : read_mem_bytes 8 args.descriptor t = Emit.descriptorTag desc := by
    have within : 0 + 8 ≤ Emit.descriptorBytes desc := by
      cases desc <;> simp [Emit.descriptorBytes]
    have unchanged := Emit.frame_read_offset frame args.descriptor (Emit.descriptorBytes desc) 0 8
      owned.descriptorBound owned.descriptorOwned within
    simp only [BitVec.add_zero] at unchanged
    exact unchanged.trans owned.descriptor.1
  refine ⟨tag, ?_⟩
  cases desc with
  | bool => trivial
  | uint operand | byteVector operand | byteList operand | bitVector operand | bitList operand =>
    exact header 8 operand (by simp [Emit.descriptorBytes]) (by simp [Emit.descriptorOperands])
      owned.descriptor.2
  | progressiveBitList limit =>
    cases limit with
    | none =>
      exact (Emit.frame_read_offset frame args.descriptor 32 8 8 owned.descriptorBound
        owned.descriptorOwned (by decide)).trans owned.descriptor.2
    | some operand =>
      exact ⟨(Emit.frame_read_offset frame args.descriptor 32 8 8 owned.descriptorBound
        owned.descriptorOwned (by decide)).trans owned.descriptor.2.1,
        header 16 operand (by simp [Emit.descriptorBytes]) (by simp [Emit.descriptorOperands])
          owned.descriptor.2.2⟩

/-- Seq and Union expose only the observed primitive-dispatch tag. No typed
composite payload representation is introduced by transporting that observation. -/
theorem value_preserved {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (frame : MemoryFrame (writable s args) s t) :
    Emit.ValueAt t args.value value := by
  have tag : read_mem_bytes 1 args.value t = Emit.valueTag value := by
    have within : 0 + 1 ≤ Emit.valueBytes value := by cases value <;> simp [Emit.valueBytes]
    have unchanged := Emit.frame_read_offset frame args.value (Emit.valueBytes value) 0 1
      owned.valueBound owned.valueOwned within
    simp only [BitVec.add_zero] at unchanged
    exact unchanged.trans owned.value_at.1
  refine ⟨tag, ?_⟩
  cases value with
  | bool flag =>
    exact (Emit.frame_read_offset frame args.value 2 1 1 owned.valueBound owned.valueOwned
      (by decide)).trans owned.value_at.2
  | uint number =>
    apply Emit.operand_header_preserved frame _ number
    · have bound := owned.valueBound
      change args.value.toNat + 24 ≤ 2^64 at bound
      omega
    · exact owned.valueOwned.subspan 8 16 (by simp [Emit.valueBytes])
    · exact owned.operandOwned number (List.mem_append.mpr (Or.inr (by simp [Emit.valueOperands])))
    · exact owned.value_at.2
  | bytes data =>
    have r8 := Emit.frame_read_offset frame args.value 24 8 8 owned.valueBound owned.valueOwned
      (by decide)
    have r16 := Emit.frame_read_offset frame args.value 24 16 8 owned.valueBound owned.valueOwned
      (by decide)
    change (read_mem_bytes 8 (args.value + 16#64) t).toNat = data.size ∧ _
    rw [r16, r8]
    refine ⟨owned.value_at.2.1, owned.value_at.2.2.1, ?_⟩
    exact frame.bytes _ data owned.value_at.2.2.1
      (owned.backingOwned ((read_mem_bytes 8 (args.value + 8#64) s).toNat, data.size)
        (by simp [Measure.backingSpans, Args.measure])) owned.value_at.2.2.2
  | bits data =>
    have r16 := Emit.frame_read_offset frame args.value 48 16 8 owned.valueBound owned.valueOwned
      (by decide)
    have r24 := Emit.frame_read_offset frame args.value 48 24 8 owned.valueBound owned.valueOwned
      (by decide)
    have r32 := Emit.frame_read_offset frame args.value 48 32 8 owned.valueBound owned.valueOwned
      (by decide)
    have r40 := Emit.frame_read_offset frame args.value 48 40 8 owned.valueBound owned.valueOwned
      (by decide)
    change (read_mem_bytes 8 (args.value + 24#64) t).toNat = data.bytes.size ∧ _
    rw [r24, r16, r32, r40]
    refine ⟨owned.value_at.2.1, owned.value_at.2.2.1, ?_, owned.value_at.2.2.2.2⟩
    exact frame.bytes _ data.bytes owned.value_at.2.2.1
      (owned.backingOwned ((read_mem_bytes 8 (args.value + 16#64) s).toNat, data.bytes.size)
        (by simp [Measure.backingSpans, Args.measure])) owned.value_at.2.2.2.1
  | seq _ | union _ _ => trivial

theorem backing_preserved {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (frame : MemoryFrame (writable s args) s t) :
    Measure.backingSpans t args.measure value = Measure.backingSpans s args.measure value := by
  cases value with
  | bytes data =>
    have r8 := Emit.frame_read_offset frame args.value 24 8 8 owned.valueBound owned.valueOwned
      (by decide)
    simp only [Measure.backingSpans, Args.measure, r8]
  | bits data =>
    have r16 := Emit.frame_read_offset frame args.value 48 16 8 owned.valueBound owned.valueOwned
      (by decide)
    simp only [Measure.backingSpans, Args.measure, r16]
  | _ => rfl

end SszArm.Serialize

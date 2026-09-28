import SszArm.MeasureContract
import SszArm.EmitObservations

namespace SszArm.Measure

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value Outcome)
open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame)

theorem saveWrites_subset (args : Args) (measured : Outcome NatOperand)
    (span : Span) (member : span ∈ saveWrites args) : span ∈ writesFor args measured := by
  simp only [writesFor, localWrites, stackWrites, List.mem_append]
  exact Or.inl (Or.inl (Or.inl member))

theorem stackWrites_subset (args : Args) (measured : Outcome NatOperand)
    (span : Span) (member : span ∈ stackWrites args measured) : span ∈ writesFor args measured := by
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl member)))

theorem bodyWrites_subset (args : Args) (measured : Outcome NatOperand)
    (span : Span) (member : span ∈ bodyWrites args measured) : span ∈ writesFor args measured := by
  simp only [bodyWrites, writesFor, localWrites, stackWrites, List.mem_append] at member ⊢
  rcases member with (lowering | result) | allocation
  · exact Or.inl (Or.inl (Or.inr lowering))
  · exact Or.inl (Or.inr result)
  · exact Or.inr allocation

theorem Owned.operand_at {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (operand : NatOperand)
    (member : operand ∈ Emit.descriptorOperands desc ++ Emit.valueOperands value) :
    operand.At (widthLoad s) := by
  rcases List.mem_append.mp member with descriptor | value
  · exact Emit.descriptor_operand_at owned.descriptor operand descriptor
  · exact Emit.value_operand_at owned.value_at operand value

/-- A framed read inside a live field need not own the enum padding before it. -/
theorem frame_read_subspan {writes : List Span} {s t : ArmState}
    (frame : MemoryFrame writes s t) (address : BitVec 64) (start total displacement bytes : Nat)
    (bound : address.toNat + start + total ≤ 2^64)
    (owned : Protected writes (address.toNat + start) total)
    (within : start ≤ displacement ∧ displacement + bytes ≤ start + total) :
    read_mem_bytes bytes (address + BitVec.ofNat 64 displacement) t =
      read_mem_bytes bytes (address + BitVec.ofNat 64 displacement) s := by
  by_cases empty : bytes = 0
  · subst bytes
    apply BitVec.eq_of_toNat_eq
    rfl
  · have position : (address + BitVec.ofNat 64 displacement).toNat =
        address.toNat + displacement := by bv_omega
    apply frame.read
    · rw [position]
      omega
    · rw [position]
      have sub := owned.subspan (displacement - start) bytes (by omega)
      have same : address.toNat + start + (displacement - start) =
          address.toNat + displacement := by omega
      simpa only [same] using sub

def descriptorLength : Desc → Nat
  | .bool => 8
  | .progressiveBitList none => 16
  | .progressiveBitList (some _) => 32
  | _ => 24

theorem descriptorSpans_eq (args : Args) (desc : Desc) :
    descriptorSpans args desc = [(args.descriptor.toNat, descriptorLength desc)] := by
  cases desc with
  | progressiveBitList cap => cases cap <;> rfl
  | _ => rfl

theorem Owned.descriptor_bound {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) : args.descriptor.toNat + descriptorLength desc ≤ 2^64 :=
  owned.descriptorBound (args.descriptor.toNat, descriptorLength desc)
    (by simp only [descriptorSpans_eq, List.mem_singleton])

theorem Owned.descriptor_protected {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) :
    Protected (writesFor args (outcome s args desc value)) args.descriptor.toNat
      (descriptorLength desc) :=
  owned.descriptorOwned (args.descriptor.toNat, descriptorLength desc)
    (by simp only [descriptorSpans_eq, List.mem_singleton])

theorem Owned.value_read {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value)
    (frame : MemoryFrame (writesFor args (outcome s args desc value)) s t)
    (start total displacement bytes : Nat)
    (member : (args.value.toNat + start, total) ∈ valueSpans args value)
    (within : start ≤ displacement ∧ displacement + bytes ≤ start + total) :
    read_mem_bytes bytes (args.value + BitVec.ofNat 64 displacement) t =
      read_mem_bytes bytes (args.value + BitVec.ofNat 64 displacement) s :=
  frame_read_subspan frame args.value start total displacement bytes
    (owned.valueBound _ member) (owned.valueOwned _ member) within

theorem descriptor_preserved {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value)
    (frame : MemoryFrame (writesFor args (outcome s args desc value)) s t) :
    Emit.DescriptorAt t args.descriptor desc := by
  have header : ∀ displacement operand, displacement + 16 ≤ descriptorLength desc →
      operand ∈ Emit.descriptorOperands desc →
      SszNative.NatArithmetic.operandAt (widthLoad s) (args.descriptor.toNat + displacement) operand →
      SszNative.NatArithmetic.operandAt (widthLoad t) (args.descriptor.toNat + displacement) operand := by
    intro displacement operand within member input
    apply Emit.operand_header_preserved frame _ operand
    · have bound := owned.descriptor_bound
      omega
    · exact owned.descriptor_protected.subspan displacement 16 within
    · exact owned.operandOwned operand (List.mem_append.mpr (Or.inl member))
    · exact input
  have tag : read_mem_bytes 8 args.descriptor t = Emit.descriptorTag desc := by
    have within : 0 + 8 ≤ descriptorLength desc := by
      cases desc with
      | progressiveBitList cap => cases cap <;> simp [descriptorLength]
      | _ => simp [descriptorLength]
    have unchanged := Emit.frame_read_offset frame args.descriptor (descriptorLength desc) 0 8
      owned.descriptor_bound owned.descriptor_protected within
    simp only [BitVec.add_zero] at unchanged
    exact unchanged.trans owned.descriptor.1
  refine ⟨tag, ?_⟩
  cases desc with
  | bool => trivial
  | uint operand | byteVector operand | byteList operand | bitVector operand | bitList operand =>
    exact header 8 operand (by simp [descriptorLength]) (by simp [Emit.descriptorOperands])
      owned.descriptor.2
  | progressiveBitList cap =>
    cases cap with
    | none =>
      exact (Emit.frame_read_offset frame args.descriptor 16 8 8 owned.descriptor_bound
        owned.descriptor_protected (by decide)).trans owned.descriptor.2
    | some operand =>
      exact ⟨(Emit.frame_read_offset frame args.descriptor 32 8 8 owned.descriptor_bound
        owned.descriptor_protected (by decide)).trans owned.descriptor.2.1,
        header 16 operand (by simp [descriptorLength]) (by simp [Emit.descriptorOperands])
          owned.descriptor.2.2⟩

theorem value_preserved {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value)
    (frame : MemoryFrame (writesFor args (outcome s args desc value)) s t) :
    Emit.ValueAt t args.value value := by
  have tag : read_mem_bytes 1 args.value t = Emit.valueTag value := by
    cases value with
    | bool flag =>
      have unchanged := owned.value_read frame 0 2 0 1 (by simp [valueSpans]) (by decide)
      simp only [BitVec.add_zero] at unchanged
      exact unchanged.trans owned.value_at.1
    | uint number | bytes number | bits number | seq number =>
      have unchanged := owned.value_read frame 0 1 0 1 (by simp [valueSpans]) (by decide)
      simp only [BitVec.add_zero] at unchanged
      exact unchanged.trans owned.value_at.1
    | union selector content =>
      have unchanged := owned.value_read frame 0 1 0 1 (by simp [valueSpans]) (by decide)
      simp only [BitVec.add_zero] at unchanged
      exact unchanged.trans owned.value_at.1
  refine ⟨tag, ?_⟩
  cases value with
  | bool flag =>
    exact (owned.value_read frame 0 2 1 1 (by simp [valueSpans]) (by decide)).trans owned.value_at.2
  | uint number =>
    apply Emit.operand_header_preserved frame _ number
    · exact owned.valueBound (args.value.toNat + 8, 16) (by simp [valueSpans])
    · exact owned.valueOwned (args.value.toNat + 8, 16) (by simp [valueSpans])
    · exact owned.operandOwned number (List.mem_append.mpr (Or.inr (by simp [Emit.valueOperands])))
    · exact owned.value_at.2
  | bytes data =>
    have r8 := owned.value_read frame 8 16 8 8 (by simp [valueSpans]) (by decide)
    have r16 := owned.value_read frame 8 16 16 8 (by simp [valueSpans]) (by decide)
    change (read_mem_bytes 8 (args.value + 16#64) t).toNat = data.size ∧ _
    rw [r16, r8]
    refine ⟨owned.value_at.2.1, owned.value_at.2.2.1, ?_⟩
    exact frame.bytes _ data owned.value_at.2.2.1
      (owned.backingOwned ((read_mem_bytes 8 (args.value + 8#64) s).toNat, data.size)
        (by simp [backingSpans])) owned.value_at.2.2.2
  | bits data =>
    have r16 := owned.value_read frame 16 32 16 8 (by simp [valueSpans]) (by decide)
    have r24 := owned.value_read frame 16 32 24 8 (by simp [valueSpans]) (by decide)
    have r32 := owned.value_read frame 16 32 32 8 (by simp [valueSpans]) (by decide)
    have r40 := owned.value_read frame 16 32 40 8 (by simp [valueSpans]) (by decide)
    change (read_mem_bytes 8 (args.value + 24#64) t).toNat = data.bytes.size ∧ _
    rw [r24, r16, r32, r40]
    refine ⟨owned.value_at.2.1, owned.value_at.2.2.1, ?_, owned.value_at.2.2.2.2⟩
    exact frame.bytes _ data.bytes owned.value_at.2.2.1
      (owned.backingOwned ((read_mem_bytes 8 (args.value + 16#64) s).toNat, data.bytes.size)
        (by simp [backingSpans])) owned.value_at.2.2.2.1
  | seq _ | union _ _ => trivial

theorem backing_preserved {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value)
    (frame : MemoryFrame (writesFor args (outcome s args desc value)) s t) :
    backingSpans t args value = backingSpans s args value := by
  cases value with
  | bytes data =>
    have r8 := owned.value_read frame 8 16 8 8 (by simp [valueSpans]) (by decide)
    simp only [backingSpans, r8]
  | bits data =>
    have r16 := owned.value_read frame 16 32 16 8 (by simp [valueSpans]) (by decide)
    simp only [backingSpans, r16]
  | _ => rfl

end SszArm.Measure

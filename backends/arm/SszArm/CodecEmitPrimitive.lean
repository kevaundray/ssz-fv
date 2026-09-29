import SszArm.CodecEmitContract

namespace SszArm.Codec.Emit

open SszNative.Codec (Desc Value)
open SszNative.CodecMeasure (Plan)
open Delimited (Span Protected)

private theorem primitive_expected (shape : SszNative.Serialize.Desc) (value : Value)
    (retain : Bool) (plan : Plan)
    (generated : SszNative.CodecEmit.Generated (.primitive shape) value retain plan) :
    SszNative.Serialize.expectedSize shape value.toPrimitive = .ok plan.size.value := by
  cases generated with
  | primitive _ _ _ _ semantic => exact semantic
  | parts _ _ _ _ _ _ _ _ shape _ _ _ _ _ => cases shape

theorem primitive_stack_cover (args : Args) (shape : SszNative.Serialize.Desc)
    (low : 176 ≤ args.stack.toNat) :
    BitVector.Covers (stackWrites args (.primitive shape)) (SszArm.Emit.stackWrites args.primitive) := by
  intro span member
  simp only [SszArm.Emit.stackWrites, Args.primitive, List.mem_cons, List.mem_singleton] at member
  rcases member with rfl | rfl <;>
    refine ⟨(args.stack.toNat - 176, 176), by simp [stackWrites, stackBytes, Stack.envelope], ?_, ?_⟩ <;>
    simp only [Prod.fst, Prod.snd] <;> omega

theorem primitive_writes_cover (args : Args) (shape : SszNative.Serialize.Desc) (size : Nat)
    (low : 176 ≤ args.stack.toNat) :
    BitVector.Covers (writesFor args (.primitive shape) size)
      (SszArm.Emit.writesFor args.primitive size) := by
  intro span member
  simp only [SszArm.Emit.writesFor, List.mem_append] at member
  rcases member with stack | result | output
  · obtain ⟨outer, member, first, last⟩ := primitive_stack_cover args shape low span stack
    exact ⟨outer, by simp [writesFor, member], first, last⟩
  · refine ⟨span, ?_, Nat.le_refl _, Nat.le_refl _⟩
    simp only [writesFor, List.mem_append]
    exact Or.inr (Or.inl result)
  · by_cases empty : size = 0
    · simp [empty] at output
    · have same : span = (args.output.toNat, size) := by
        simpa only [empty, ↓reduceIte, Args.primitive, List.mem_singleton] using output
      subst span
      exact ⟨(args.output.toNat, size), by simp [writesFor, empty], Nat.le_refl _, Nat.le_refl _⟩

theorem Owned.primitive {s : ArmState} {args : Args} {shape : SszNative.Serialize.Desc}
    {value : Value} {retain : Bool} {plan : Plan} {supplied : Option Plan}
    (owned : Owned s args (.primitive shape) value retain plan supplied) :
    SszArm.Emit.Owned s args.primitive shape value.toPrimitive plan.size.value := by
  have low : 176 ≤ args.stack.toNat := owned.stackLow
  have cover := primitive_writes_cover args shape plan.size.value low
  have stackCover := primitive_stack_cover args shape low
  have inputs := Storage.primitive_inputs (args := args.primitive) owned.descriptor owned.value_at
  refine ⟨primitive_expected shape value retain plan owned.valid.generated,
    lt_of_le_of_lt owned.fitting args.capacity.isLt, owned.fitting,
    inputs.physical, inputs.descriptorBound, inputs.descriptor,
    inputs.valueBound, inputs.value_at, by have := owned.resultBound; dsimp [Args.primitive]; omega,
    owned.outputBound, low, ?_, stackCover.protected owned.outputStack,
    owned.outputResult, cover.protected inputs.descriptorOwned,
    cover.protected inputs.valueOwned, ?_, ?_⟩
  · exact stackCover.protected (owned.resultStack.subspan 0 68 (by decide))
  · intro operand member
    exact cover.operand operand (inputs.operandOwned operand member)
  · intro span member
    exact cover.protected (inputs.backingOwned span member)

private theorem bytes_byteMemory {s : ArmState} {address : Nat} {bytes : Ssz.Bytes}
    (stored : SszNative.ByteView.BytesAt (UintCodec.widthLoad s) address bytes)
    (index : Nat) (inside : index < bytes.size) :
    byteMemory s (address + index) = some bytes[index] := by
  apply congrArg some
  apply UInt8.toNat_inj.mp
  have word := stored index inside
  simp only [UintCodec.widthLoad, Array.getElem?_eq_getElem inside, Option.getD_some,
    Option.some.injEq] at word
  exact word

private theorem primitive_output {s t : ArmState} {shape : SszNative.Serialize.Desc}
    {value : Value} {retain : Bool} {plan : Plan} {supplied : Option Plan}
    (owned : Owned s (Args.ofEntry s) (.primitive shape) value retain plan supplied)
    (post : SszArm.Emit.Post s t shape value.toPrimitive plan.size.value) :
    OutputMatches s t (Args.ofEntry s) (.primitive shape) value supplied := by
  have expected := primitive_expected shape value retain plan owned.valid.generated
  obtain ⟨bytes, semantic, size, stored, _, _⟩ := post.encoding expected
  have semantic' : Ssz.serialize (Desc.primitive shape).erase value.erase = .ok bytes := by
    simpa only [Desc.erase, Value.erase_toPrimitive] using semantic
  have encoded := SszNative.CodecEmit.generated_emit_encodes (.primitive shape) value retain
    plan supplied (Args.ofEntry s).out bytes owned.valid.generated owned.valid.usable
    owned.valid.children owned.valid.leading owned.fitting (Args.ofEntry s).capacity.isLt semantic'
  intro index inside
  by_cases prefix : index < bytes.size
  · rw [encoded.initialized (byteMemory s) index prefix]
    exact bytes_byteMemory stored index prefix
  · rw [encoded.frame (byteMemory s) _ (Or.inr (by omega))]
    have tail := post.tail index (by omega) inside
    simp only [byteMemory, BoolCodec.read_one, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
    exact congrArg (fun word => some (UInt8.ofBitVec word)) tail

/-- The existing seven-shape machine theorem is a genuine base case of the
recursive contract. Its original-entry execution is reused, not hypothesized. -/
theorem primitive_program_correct (s : ArmState) (base : BitVec 64)
    (shape : SszNative.Serialize.Desc) (value : Value) (retain : Bool)
    (plan : Plan) (supplied : Option Plan)
    (owned : Owned s (Args.ofEntry s) (.primitive shape) value retain plan supplied)
    (code : SszArm.Emit.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    ∃ fuel, Post s (run fuel s) (.primitive shape) value plan supplied := by
  have legacyOwned : SszArm.Emit.Owned s (SszArm.Emit.Args.ofEntry s)
      shape value.toPrimitive plan.size.value := owned.primitive
  obtain ⟨fuel, post⟩ := SszArm.Emit.program_correct s base shape value.toPrimitive
    plan.size.value legacyOwned code error aligned pc
  have frame := (primitive_writes_cover (Args.ofEntry s) shape plan.size.value owned.stackLow).frame post.frame
  exact ⟨fuel, post.returned, post.length, post.status, primitive_output owned post, frame,
    Storage.desc_preserved owned.descriptor frame,
    Storage.value_preserved owned.value_at frame, plan_preserved owned.plan frame⟩

end SszArm.Codec.Emit

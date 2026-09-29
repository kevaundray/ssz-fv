import SszX86.CodecStorage

set_option autoImplicit false

namespace SszX86.Codec
open SszNative UintCodec

/-- Recover the old primitive observation without losing the stronger recursive
premise. For composites this is used only by the primitive wrong-kind branch. -/
theorem ValueAt.toPrimitive {m : DataMem} {r : Footprint} {p : BitVec 64}
    {value : SszNative.Codec.Value} (h : ValueAt m r p value) :
    ∃ buffer, PrimitiveValueAt m r p buffer value.toPrimitive := by
  cases h with
  | valueBool h | valueUint h | valueBytes h | valueBits h => exact ⟨_, h⟩
  | valueSeq header slice children =>
    refine ⟨0, ⟨⟨header.tag.load, True.intro⟩, header.span, ?_⟩⟩
    intro a borrowed
    exact False.elim borrowed
  | valueUnion header selector pointer child =>
    refine ⟨0, ⟨⟨header.tag.load, True.intro⟩, header.span, ?_⟩⟩
    intro a borrowed
    exact False.elim borrowed

theorem ValueAt.tag {m : DataMem} {r : Footprint} {p : BitVec 64}
    {value : SszNative.Codec.Value} (h : ValueAt m r p value) :
    Mem.loadInt m p 1 = some (Emit.valueTag value.toPrimitive : Int) := by
  obtain ⟨buffer, primitive⟩ := h.toPrimitive
  exact primitive.stored.1

/-- The original Emit footprint is a subset of the recursive caller's readonly
footprint. The reverse inclusion is deliberately false for composite values. -/
theorem primitiveBorrowed {s : MachineData} {r : Footprint}
    {desc : SszNative.Serialize.Desc} {value : SszNative.Serialize.Value} {buffer : BitVec 64}
    (descriptor : PrimitiveDescAt s.dmem r s.regs.rsi.toBitVec desc)
    (stored : PrimitiveValueAt s.dmem r s.regs.rdx.toBitVec buffer value) :
    ∀ a, Emit.Borrowed s desc value buffer a → r a := by
  intro a borrowed
  rcases borrowed with descriptorSpan | valueSpan | descriptorLimbs | valueBytes
  · apply descriptor.span.covered a
    rcases descriptorSpan with ⟨i, hi, equal⟩
    refine ⟨i, ?_, equal⟩
    have bytes : Emit.descBytes desc ≤ 40 := by cases desc <;> decide
    omega
  · apply stored.span.covered a
    rcases valueSpan with ⟨i, hi, equal⟩
    refine ⟨i, ?_, equal⟩
    have bytes : Emit.valueBytes value ≤ 48 := by cases value <;> decide
    omega
  · exact descriptor.borrowed a descriptorLimbs
  · exact stored.borrowed a valueBytes

/-- Exact original-register ABI and readonly adapter for existing primitive
Owned constructors. It does not manufacture a successful logical call. -/
theorem primitiveInputs {s : MachineData} {r : Footprint}
    {desc : SszNative.Serialize.Desc} {value : SszNative.Codec.Value}
    (descriptor : DescAt s.dmem r s.regs.rsi.toBitVec (.primitive desc))
    (stored : ValueAt s.dmem r s.regs.rdx.toBitVec value) :
    ∃ buffer, Emit.DescAt s.dmem s.regs.rsi.toBitVec desc ∧
      Emit.ValueAt s.dmem s.regs.rdx.toBitVec buffer value.toPrimitive ∧
      (∀ a, Emit.Borrowed s desc value.toPrimitive buffer a → r a) := by
  obtain ⟨buffer, primitive⟩ := stored.toPrimitive
  cases descriptor with
  | descPrimitive descriptor =>
    exact ⟨buffer, descriptor.stored, primitive.stored, primitiveBorrowed descriptor primitive⟩

end SszX86.Codec

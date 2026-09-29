import SszX86.CodecEmitInvariant
import SszX86.CodecStorage
import SszX86.EmitBodies

set_option autoImplicit false

namespace SszX86.CodecEmit
open SszNative UintCodec

/-- Resources at the actual primitive body cut. Unlike the historical complete
entry wrapper this requires only the eight-byte active result, never an 80-byte
sret exclusion. All original readonly aliases remain in the common footprint. -/
structure LeafOwned (s : MachineData) (shape : Serialize.Desc)
    (value : SszNative.Codec.Value) (supplied : Option SszNative.CodecMeasure.Plan)
    (r : SszX86.Codec.Footprint) (buffer : BitVec 64)
    (call : GeneratedCall (.primitive shape) value supplied s.regs.r9.toNat) : Prop where
  tag : Emit.BodyTag shape value.toPrimitive s
  physical : value.Physical
  descriptor : SszX86.Codec.PrimitiveDescAt s.dmem r s.regs.rsi.toBitVec shape
  valueStored : SszX86.Codec.PrimitiveValueAt s.dmem r s.regs.r12.toBitVec buffer value.toPrimitive
  outputBound : s.regs.r14.toNat + call.measured.size.value ≤ 2 ^ 64
  resultBound : s.regs.rbx.toNat + 8 ≤ 2 ^ 64
  output : Large.Mapped s.dmem s.regs.r14.toBitVec call.measured.size.value
  result : Large.Mapped s.dmem s.regs.rbx.toBitVec 8
  stack : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 8) 112
  outputResult : Large.Disjoint s.regs.r14.toBitVec s.regs.rbx.toBitVec call.measured.size.value 8
  outputStack : Large.Disjoint s.regs.r14.toBitVec (s.regs.rsp.toBitVec - 8)
    call.measured.size.value 112
  resultStack : Large.Disjoint s.regs.rbx.toBitVec (s.regs.rsp.toBitVec - 8) 8 112
  readonly : ∀ a, r a → ¬ Emit.BodyWritable s call.measured.size.value a

theorem LeafOwned.bool {s : MachineData} {value : Bool}
    {supplied : Option SszNative.CodecMeasure.Plan} {r : SszX86.Codec.Footprint}
    {buffer : BitVec 64}
    {call : GeneratedCall (.primitive .bool) (.bool value) supplied s.regs.r9.toNat}
    (h : LeafOwned s .bool (.bool value) supplied r buffer call) : Emit.BoolOwned s value := by
  have size : 1 = call.measured.size.value := Except.ok.inj call.primitive_valid.success
  refine ⟨h.tag.2 (by decide), by have := call.fits; omega,
    h.valueStored.stored.2, ?_, h.result, ?_⟩
  · simpa only [← size] using h.output
  · simpa only [← size] using h.outputResult

theorem LeafOwned.uint {s : MachineData} {width number : NatOperand}
    {supplied : Option SszNative.CodecMeasure.Plan} {r : SszX86.Codec.Footprint}
    {buffer : BitVec 64}
    {call : GeneratedCall (.primitive (.uint width)) (.uint number) supplied s.regs.r9.toNat}
    (h : LeafOwned s (.uint width) (.uint number) supplied r buffer call) :
    Emit.Uint.Owned s width number call.measured.size.value := by
  refine {
    tag := h.tag.2 (by decide)
    widthAt := h.descriptor.stored.2
    numberAt := h.valueStored.stored.2
    valid := call.primitive_valid.success
    capacity := call.fits
    width_bound := ?_
    number_bound := ?_
    output_bound := h.outputBound
    result_bound := h.resultBound
    output := h.output
    result := h.result
    apart := ?_
    readonly := ?_ }
  · have bound := h.descriptor.span.bound
    simp only [UInt64.toNat_toBitVec] at bound
    omega
  · have bound := h.valueStored.span.bound
    simp only [UInt64.toNat_toBitVec] at bound
    omega
  · intro a output result
    obtain ⟨i, hi, first⟩ := output
    obtain ⟨j, hj, second⟩ := result
    exact h.outputResult i hi j hj (first.symm.trans second)
  · intro a borrowed writes
    apply h.readonly a ?_ (writes.imp_right Or.inl)
    rcases borrowed with widthBorrow | numberBorrow
    · rcases widthBorrow with header | limbs
      · exact h.descriptor.span.covered a (Emit.span_shift _ 8 16 40 (by decide) header)
      · exact h.descriptor.borrowed a limbs
    · rcases numberBorrow with header | limbs
      · exact h.valueStored.span.covered a (Emit.span_shift _ 8 16 48 (by decide) header)
      · exact h.valueStored.borrowed a limbs

theorem LeafOwned.bytes {s : MachineData} {shape : Serialize.Desc} {bytes : Ssz.Bytes}
    {supplied : Option SszNative.CodecMeasure.Plan} {r : SszX86.Codec.Footprint}
    {buffer : BitVec 64}
    {call : GeneratedCall (.primitive shape) (.bytes bytes) supplied s.regs.r9.toNat}
    (h : LeafOwned s shape (.bytes bytes) supplied r buffer call) : Emit.Bytes.Owned s bytes buffer := by
  have valid := call.primitive_valid
  have compatible := Emit.success_compatible shape (.bytes bytes) _ valid.success
  have kind : Emit.descTag shape = 2 ∨ Emit.descTag shape = 3 := by
    cases shape <;> simp_all [Emit.Compatible, Emit.descTag]
  have encoding : Serialize.emit shape (.bytes bytes) = bytes := by
    cases shape <;> simp_all [Emit.Compatible, Serialize.emit]
  have size : call.measured.size.value = bytes.size := by
    have measured := valid.emitted_size
    rw [encoding] at measured
    exact measured.symm
  refine {
    tag := ?_
    capacity := by have := call.fits; omega
    length := h.valueStored.stored.2.2.1
    pointer := h.valueStored.stored.2.1
    source := h.valueStored.stored.2.2.2.1
    output := by simpa only [size] using h.output
    result := h.result
    stack := fun i hi => h.stack i (by omega)
    outputResult := by simpa only [size] using h.outputResult
    outputStack := ?_
    resultStack := fun i hi j hj => h.resultStack i hi j (by omega)
    sourceOutput := ?_
    sourceStack := ?_ }
  · rcases kind with vector | list
    · exact Or.inl (by simpa only [vector] using h.tag.1)
    · exact Or.inr (by simpa only [list] using h.tag.1)
  · intro i hi j hj
    exact h.outputStack i (by omega) j (by omega)
  · intro i hi j hj equal
    apply h.readonly _ (h.valueStored.borrowed _ ⟨i, hi, rfl⟩)
    exact Or.inl ⟨j, by omega, equal⟩
  · intro i hi j hj equal
    apply h.readonly _ (h.valueStored.borrowed _ ⟨i, hi, rfl⟩)
    exact Or.inr (Or.inr ⟨j, by omega, equal⟩)

theorem LeafOwned.bits {s : MachineData} {shape : Serialize.Desc} {bits : Serialize.Packed}
    {supplied : Option SszNative.CodecMeasure.Plan} {r : SszX86.Codec.Footprint}
    {buffer : BitVec 64}
    {call : GeneratedCall (.primitive shape) (.bits bits) supplied s.regs.r9.toNat}
    (h : LeafOwned s shape (.bits bits) supplied r buffer call) :
    Emit.Bits.Owned s shape bits buffer call.measured.size.value := by
  have valid := call.primitive_valid
  have kind : Emit.Bits.IsBits shape := by
    have compatible := Emit.success_compatible shape (.bits bits) _ valid.success
    cases shape <;> simp_all [Emit.Compatible, Emit.Bits.IsBits]
  refine {
    kind := kind
    valid := valid
    tag := h.tag.1
    physical := h.physical
    pointer := h.valueStored.stored.2.1
    length := h.valueStored.stored.2.2.1
    low := h.valueStored.stored.2.2.2.1
    high := h.valueStored.stored.2.2.2.2.1
    source := h.valueStored.stored.2.2.2.2.2.1
    outputMapped := h.output
    resultMapped := h.result
    stackMapped := h.stack
    outputResult := h.outputResult
    outputStack := h.outputStack
    resultStack := h.resultStack
    headerProtected := fun a inside => h.readonly a (h.valueStored.span.covered a inside)
    sourceProtected := fun a inside => h.readonly a (h.valueStored.borrowed a inside) }

end SszX86.CodecEmit

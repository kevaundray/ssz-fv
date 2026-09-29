import SszX86.CodecEmitLeafEntry
import SszX86.CodecEmitLeafOwned

set_option autoImplicit false

namespace SszX86.CodecEmit
open SszNative UintCodec

/-- Transfer only the capacity index; the generated witness and actual retained
plan stay exactly the original ones. -/
def callAtBody {s t : MachineData} {base : Int64} {shape : Serialize.Desc}
    {value : SszNative.Codec.Value} {supplied : Option SszNative.CodecMeasure.Plan}
    {r : SszX86.Codec.Footprint} {ra : BitVec 64}
    (owned : Owned s base (.primitive shape) value supplied r ra) (anchors : Emit.AtBody s t) :
    GeneratedCall (.primitive shape) value supplied t.regs.r9.toNat :=
  { owned.call with
    fits := by simpa only [anchors.capacity] using owned.call.fits
    host := by simpa only [anchors.capacity] using owned.call.host }

theorem body_writable_sub {s t : MachineData} {desc : SszNative.Codec.Desc} {written : Nat}
    (anchors : Emit.AtBody s t) (a : BitVec 64) (inside : Emit.BodyWritable t written a) :
    Writable s desc written a := by
  have original := anchors.body_writable inside
  rcases original with output | result | status | scratch
  · exact Or.inl output
  · exact Or.inr (Or.inl result)
  · exact Or.inr (Or.inr (Or.inl status))
  · apply Or.inr; apply Or.inr; apply Or.inr
    have included := SszX86.Codec.stack_subspan s.regs.rsp.toBitVec 0 160
      (stackBytes desc) (by have := stackBytes_min desc; omega) a
    apply included
    simpa only [SszX86.Codec.StackWrites, BitVec.ofNat_zero, BitVec.sub_zero,
      BitVec.ofNat_eq_ofNat] using scratch

theorem body_stack_sub {s t : MachineData} {desc : SszNative.Codec.Desc}
    (anchors : Emit.AtBody s t) (a : BitVec 64)
    (inside : Emit.InSpan a (t.regs.rsp.toBitVec - 8) 112) :
    SszX86.Codec.StackWrites s.regs.rsp.toBitVec (stackBytes desc) a := by
  rw [anchors.local_base] at inside
  have widened : Emit.InSpan a (s.regs.rsp.toBitVec - 160) 160 := by
    obtain ⟨i, hi, equal⟩ := inside
    exact ⟨i, by omega, equal⟩
  have included := SszX86.Codec.stack_subspan s.regs.rsp.toBitVec 0 160
    (stackBytes desc) (by have := stackBytes_min desc; omega) a
  apply included
  simpa only [SszX86.Codec.StackWrites, BitVec.ofNat_zero, BitVec.sub_zero,
    BitVec.ofNat_eq_ofNat] using widened

/-- Actual entry anchors and original 72-byte-result resources derive all leaf
body resources. No footprint extension beyond the native result object occurs. -/
theorem leaf_resources {s t : MachineData} {base : Int64} {shape : Serialize.Desc}
    {value : SszNative.Codec.Value} {supplied : Option SszNative.CodecMeasure.Plan}
    {r : SszX86.Codec.Footprint} {ra : BitVec 64}
    (owned : Owned s base (.primitive shape) value supplied r ra)
    (anchors : Emit.AtBody s t) (tag : Emit.BodyTag shape value.toPrimitive t) :
    ∃ buffer, LeafOwned t shape value supplied r buffer (callAtBody owned anchors) := by
  have readonly : ∀ a, r a →
      ¬ SszX86.Codec.StackWrites s.regs.rsp.toBitVec (stackBytes (.primitive shape)) a := by
    intro a borrowed inside
    exact owned.readonly a borrowed (Or.inr (Or.inr (Or.inr inside)))
  have descStored : SszX86.Codec.DescAt t.dmem r t.regs.rsi.toBitVec (.primitive shape) := by
    rw [anchors.memory, anchors.descriptorPointer]
    exact owned.descriptor.savedSix _ (by have := stackBytes_min (.primitive shape); omega) readonly
  have valueStored : SszX86.Codec.ValueAt t.dmem r t.regs.r12.toBitVec value := by
    rw [anchors.memory, anchors.valuePointer]
    exact owned.valueStored.savedSix _ (by have := stackBytes_min (.primitive shape); omega) readonly
  obtain ⟨buffer, primitiveValue⟩ := valueStored.toPrimitive
  have primitiveDesc : SszX86.Codec.PrimitiveDescAt t.dmem r t.regs.rsi.toBitVec shape := by
    cases descStored with
    | descPrimitive stored => exact stored
  refine ⟨buffer, {
    tag := tag
    physical := owned.physical
    descriptor := primitiveDesc
    valueStored := primitiveValue
    outputBound := ?_
    resultBound := ?_
    output := ?_
    result := ?_
    stack := ?_
    outputResult := ?_
    outputStack := ?_
    resultStack := ?_
    readonly := ?_ }⟩
  · rw [anchors.output]
    have bound := owned.outputBound
    have fits := owned.call.fits
    change s.regs.r8.toNat + owned.call.measured.size.value ≤ 2 ^ 64
    omega
  · rw [anchors.result]
    have bound := owned.resultBound
    omega
  · rw [anchors.memory, anchors.output]
    exact Dispatch.saved_mapped s _ _ owned.outputMapped
  · rw [anchors.memory, anchors.result]
    exact Dispatch.saved_mapped s _ _ owned.lengthMapped
  · rw [anchors.memory, anchors.local_base]
    have original := (owned.stack.substack 0 160 (stackBytes_min _)).mapped
    have mapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 160) 160 := by
      simpa only [BitVec.ofNat_zero, BitVec.sub_zero, BitVec.ofNat_eq_ofNat] using original
    have saved := Dispatch.saved_mapped s _ _ mapped
    exact fun i hi => saved i (by omega)
  · rw [anchors.output, anchors.result]
    intro i hi j hj
    exact owned.outputResult i (by have := owned.call.fits; exact Nat.lt_of_lt_of_le hi this)
      j (by omega)
  · intro i hi j hj equal
    have inside := body_stack_sub (desc := .primitive shape) anchors _
      (show Emit.InSpan (t.regs.rsp.toBitVec - 8 + BitVec.ofNat 64 j)
        (t.regs.rsp.toBitVec - 8) 112 from ⟨j, hj, rfl⟩)
    obtain ⟨k, hk, atStack⟩ := inside
    apply owned.outputStack i (by have := owned.call.fits; exact Nat.lt_of_lt_of_le hi this)
      k (by omega)
    rw [← anchors.output]
    exact equal.trans atStack
  · intro i hi j hj equal
    have inside := body_stack_sub (desc := .primitive shape) anchors _
      (show Emit.InSpan (t.regs.rsp.toBitVec - 8 + BitVec.ofNat 64 j)
        (t.regs.rsp.toBitVec - 8) 112 from ⟨j, hj, rfl⟩)
    obtain ⟨k, hk, atStack⟩ := inside
    apply owned.resultStack i (by omega) k (by omega)
    rw [← anchors.result]
    exact equal.trans atStack
  · intro a borrowed inside
    exact owned.readonly a borrowed (body_writable_sub anchors a inside)

end SszX86.CodecEmit

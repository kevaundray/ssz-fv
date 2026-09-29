import SszX86.CodecSerializeMeasureOwned
import SszX86.CodecMeasureEffectsProofs
import SszX86.SerializeMeasured

namespace SszX86.CodecSerialize
open SszNative UintCodec

/-- Measurement publishes its result within the wrapper stack. Outside that
stack only initialized effects and the arena cursor can change. -/
def MeasuredWrites (s : MachineData) (desc : SszNative.Codec.Desc)
    (value : SszNative.Codec.Value) (address capacity used : BitVec 64) : Codec.Footprint := fun a =>
  CodecMeasure.EffectsWrite (measured desc value address capacity used).effects a ∨
  Codec.InSpan a (s.regs.r9.toBitVec + 16) 8 ∨
  Codec.StackWrites s.regs.rsp.toBitVec (stackBytes desc) a

section
variable {s : MachineData} {base : Int64}
    {desc : SszNative.Codec.Desc} {value : SszNative.Codec.Value} {readonly : Codec.Footprint}
    {address capacity used ra : BitVec 64} {t : MachineState}

theorem measured_anchors
    (post : CodecMeasure.Post (Serialize.measureState s base) desc value readonly
      address capacity used (base + 47).toBitVec true t) : Serialize.MeasureAnchors s base t := by
  refine ⟨?_, ?_, post.abi.rbx, post.abi.r12, post.abi.r13,
    post.abi.r14, post.abi.r15, post.abi.rbp, post.abi.vectors⟩
  · simpa only [Int64.ofBitVec_toBitVec] using post.abi.returned
  · rw [post.abi.stack, Serialize.measureState_stack_pointer]
    unfold Serialize.wrapperSP
    bv_omega

theorem measured_mapping
    (post : CodecMeasure.Post (Serialize.measureState s base) desc value readonly
      address capacity used (base + 47).toBitVec true t) :
    BitVector.Mapping.Extends s.dmem t.1.dmem :=
  Serialize.measured_mapping post.mapping

theorem measure_writable_measured (a : BitVec 64)
    (writes : CodecMeasure.Writable (Serialize.measureState s base) desc
      (measured desc value address capacity used).effects a) :
    MeasuredWrites s desc value address capacity used a := by
  rcases writes with result | effects | cursor | activation
  · apply Or.inr ∘ Or.inr
    rw [Serialize.measureState_plan_pointer] at result
    exact stack_window s desc 112 72 (by decide)
      (by have := stackBytes_wrapper desc; omega) result
  · exact Or.inl effects
  · exact Or.inr (Or.inl cursor)
  · apply Or.inr ∘ Or.inr
    rw [Serialize.measureState_stack_pointer] at activation
    exact Codec.stack_subspan s.regs.rsp.toBitVec 144 (CodecMeasure.stackBytes desc)
      (stackBytes desc) (by rfl) a activation

theorem measured_frame
    (post : CodecMeasure.Post (Serialize.measureState s base) desc value readonly
      address capacity used (base + 47).toBitVec true t) :
    Codec.MemoryFrame s.dmem t.1.dmem (MeasuredWrites s desc value address capacity used) := by
  intro a outside
  calc
    t.1.dmem.get? a = (Serialize.measureState s base).dmem.get? a :=
      post.frame a (fun writes => outside (measure_writable_measured a writes))
    _ = s.dmem.get? a := measure_frame_stack s base desc a
      (fun inside => outside (Or.inr (Or.inr inside)))

theorem Owned.measure_effects_free
    (owned : Owned s base desc value readonly address capacity used ra) (a : BitVec 64)
    (effects : CodecMeasure.EffectsWrite (measured desc value address capacity used).effects a) :
    Codec.InSpan a (address + used) (capacity.toNat - used.toNat) :=
  CodecMeasure.Geometry.effects_in_free desc value address capacity used true owned.arenaBound a effects

theorem Owned.measured_writes_available
    (owned : Owned s base desc value readonly address capacity used ra) (a : BitVec 64)
    (writes : MeasuredWrites s desc value address capacity used a) :
    Available s desc address capacity used a := by
  rcases writes with effects | cursor | activation
  · exact Or.inr (Or.inr (Or.inr (Or.inl (owned.measure_effects_free a effects))))
  · exact Or.inr (Or.inr (Or.inl cursor))
  · exact Or.inr (Or.inr (Or.inr (Or.inr activation)))

theorem Owned.measured_borrowed
    (owned : Owned s base desc value readonly address capacity used ra)
    (post : CodecMeasure.Post (Serialize.measureState s base) desc value readonly
      address capacity used (base + 47).toBitVec true t)
    (a : BitVec 64) (borrowed : readonly a) : t.1.dmem.get? a = s.dmem.get? a :=
  measured_frame post a (fun writes =>
    owned.readonlyDisjoint a borrowed (owned.measured_writes_available a writes))

theorem measured_descriptor
    (post : CodecMeasure.Post (Serialize.measureState s base) desc value readonly
      address capacity used (base + 47).toBitVec true t) :
    Codec.DescAt t.1.dmem readonly s.regs.rsi.toBitVec desc := post.descriptor

theorem measured_value
    (post : CodecMeasure.Post (Serialize.measureState s base) desc value readonly
      address capacity used (base + 47).toBitVec true t) :
    Codec.ValueAt t.1.dmem readonly s.regs.rdx.toBitVec value := post.valueStored

end
end SszX86.CodecSerialize

import SszX86.IndicesElementTypeFields

namespace SszX86.IndicesElementType
open SszNative UintCodec

private theorem desc_tag_bound (desc : SszNative.Codec.Desc) : Codec.descTag desc < 13 := by
  cases desc with
  | primitive primitive => cases primitive <;> decide
  | vector _ _ | list _ _ | progressiveList _ _ | container _
  | progressiveContainer _ _ | compatibleUnion _ => decide

private theorem sequence_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (readonly : Codec.Footprint) (desc : SszNative.Codec.Desc)
    (path : SszNative.Indices.PathStep) (ra childPointer : BitVec 64)
    (owned : Owned s base readonly desc path ra) (preserved : Preserved s t)
    (memory : t.dmem = s.dmem) (progressive : Bool) (child : SszNative.Codec.Desc)
    (pointer : Mem.loadInt t.dmem
      (t.regs.rsi.toBitVec + if progressive then 8 else 24) 8 = some (childPointer.toNat : Int))
    (stored : Codec.DescAt s.dmem readonly childPointer child) :
    Eventually (step e) (Returned s readonly ra (.ok child))
      (t, base + if progressive then 121 else 76) := by
  apply child_pointer_cps e base hc t progressive childPointer pointer
  apply copy_runs e base hc s _ readonly desc path ra child owned preserved memory
  exact stored

/-- Complete execution of the original linked element_type entry through one
of its five actual RETs. Inputs are raw physical descriptors and PathSteps;
logical ordinal size, noncanonical high zeros and emptyLarge are unrestricted.
No intermediate state, chosen branch, future output or continuation is an
original caller premise. The copied result retains every original physical
word of its selected child, including otherwise opaque descriptor padding. -/
theorem program_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (readonly : Codec.Footprint) (desc : SszNative.Codec.Desc)
    (path : SszNative.Indices.PathStep) (ra : BitVec 64)
    (owned : Owned s base readonly desc path ra) :
    Eventually (step e) (Returned s readonly ra (SszNative.Indices.elementType desc path))
      (s, base) := by
  let tag : Fin 13 := ⟨Codec.descTag desc, desc_tag_bound desc⟩
  have pathLoad : Mem.loadInt s.dmem s.regs.rdx.toBitVec 8 =
      some ((BitVec.ofNat 64 (SszX86.Indices.Storage.pathStepTag path)).toNat : Int) := by
    have load := owned.pathStep.header.tag.load
    cases path <;> simpa [SszX86.Indices.Storage.pathStepTag] using load
  apply dispatch_cps e base hc s tag
    (BitVec.ofNat 64 (SszX86.Indices.Storage.pathStepTag path))
    owned.descriptor.tag pathLoad owned.table
  intro a c flags
  have preserved : Preserved s (dispatched s a c flags) := by constructor <;> rfl
  cases desc with
  | primitive primitive =>
    cases primitive <;> cases path <;>
      simp only [tag, Codec.descTag, Emit.descTag, SszX86.Indices.Storage.pathStepTag,
        dispatchPc, tableTarget, SszNative.Indices.elementType] <;>
      first
      | exact bool_runs e base hc s _ readonly _ _ ra owned preserved rfl
      | exact uint_runs e base hc s _ readonly _ _ ra owned preserved rfl
      | exact notSteppable_runs e base hc s _ readonly _ _ ra owned preserved rfl
  | vector child length =>
    obtain ⟨childPointer, pointer, stored⟩ := owned.descriptor.vector
    cases path <;>
      simp only [tag, Codec.descTag, SszX86.Indices.Storage.pathStepTag,
        dispatchPc, tableTarget, SszNative.Indices.elementType] <;>
      exact sequence_runs e base hc s _ readonly _ _ ra childPointer owned preserved
        rfl false child pointer.load stored
  | list child limit =>
    obtain ⟨childPointer, pointer, _, stored⟩ := owned.descriptor.list
    cases path <;>
      simp only [tag, Codec.descTag, SszX86.Indices.Storage.pathStepTag,
        dispatchPc, tableTarget, SszNative.Indices.elementType] <;>
      exact sequence_runs e base hc s _ readonly _ _ ra childPointer owned preserved
        rfl false child pointer.load stored
  | progressiveList child limit =>
    obtain ⟨childPointer, pointer, _, stored⟩ := owned.descriptor.progressiveList
    cases path <;>
      simp only [tag, Codec.descTag, SszX86.Indices.Storage.pathStepTag,
        dispatchPc, tableTarget, SszNative.Indices.elementType] <;>
      exact sequence_runs e base hc s _ readonly _ _ ra childPointer owned preserved
        rfl true child pointer.load stored
  | container fields =>
    cases path with
    | position ordinal =>
      obtain ⟨buffer, slice, stored⟩ := owned.descriptor.container
      simp only [tag, Codec.descTag, SszX86.Indices.Storage.pathStepTag,
        dispatchPc, tableTarget, SszNative.Indices.elementType]
      exact fields_runs e base hc s _ readonly _ _ ra owned preserved rfl false
        fields buffer ordinal slice stored owned.pathStep.ordinal
    | length | activeFields | selector =>
      simp only [tag, Codec.descTag, SszX86.Indices.Storage.pathStepTag,
        dispatchPc, tableTarget, SszNative.Indices.elementType]
      exact notSteppable_runs e base hc s _ readonly _ _ ra owned preserved rfl
  | progressiveContainer active fields =>
    cases path with
    | position ordinal =>
      obtain ⟨buffer, slice, stored⟩ := owned.descriptor.progressiveContainer
      simp only [tag, Codec.descTag, SszX86.Indices.Storage.pathStepTag,
        dispatchPc, tableTarget, SszNative.Indices.elementType]
      exact fields_runs e base hc s _ readonly _ _ ra owned preserved rfl true
        fields buffer ordinal slice stored owned.pathStep.ordinal
    | length | activeFields | selector =>
      simp only [tag, Codec.descTag, SszX86.Indices.Storage.pathStepTag,
        dispatchPc, tableTarget, SszNative.Indices.elementType]
      exact notSteppable_runs e base hc s _ readonly _ _ ra owned preserved rfl
  | compatibleUnion variants =>
    cases path <;>
      simp only [tag, Codec.descTag, SszX86.Indices.Storage.pathStepTag,
        dispatchPc, tableTarget, SszNative.Indices.elementType] <;>
      exact notSteppable_runs e base hc s _ readonly _ _ ra owned preserved rfl

end SszX86.IndicesElementType

import SszX86.CodecMeasurePrimitiveOwned
import SszX86.CodecMeasurePrimitive
import SszX86.CodecMeasurePrimitiveCursor
import SszX86.CodecStorageMeasure
import SszX86.SerializeProvenance
import SszX86.MeasureArenaFrame
import SszX86.MeasureFrame
import SszX86.BitVectorMappingClosure

set_option autoImplicit false

namespace SszX86.CodecMeasure
open SszNative BoolCodec UintCodec

private theorem primitive_model (shape : Serialize.Desc) (value : SszNative.Codec.Value)
    (arena : Delimited.ArenaState) (retain : Bool) :
    SszNative.CodecMeasure.measure (.primitive shape) value arena retain =
      SszNative.CodecMeasure.primitive shape value arena := by
  rw [SszNative.CodecMeasure.measure]
  rfl

private theorem primitive_stack (s : MachineData) (shape : Serialize.Desc)
    (a : BitVec 64) (inside : Emit.InSpan a (s.regs.rsp.toBitVec - 280) 280) :
    Codec.StackWrites s.regs.rsp.toBitVec (stackBytes (.primitive shape)) a := by
  have enough := stackBytes_leaf (.primitive shape)
  apply Codec.stack_subspan s.regs.rsp.toBitVec 0 280 (stackBytes (.primitive shape))
    (by omega) a
  simpa only [BitVec.ofNat_zero, BitVec.sub_zero] using inside

private theorem primitive_writes_available (s : MachineData) (shape : Serialize.Desc)
    (value : SszNative.Codec.Value) (address capacity used a : BitVec 64)
    (written : Measure.Writable s
      (Serialize.measure shape value.toPrimitive (Measure.arenaState address capacity used)) a) :
    Available s (.primitive shape) address capacity used a := by
  rcases written with result | allocation | cursor | stack
  · exact Or.inl (Measure.resultWrites_span _ _ a result)
  · exact Or.inr (Or.inr (Or.inl
      (Measure.allocation_in_free shape value.toPrimitive address capacity used a allocation)))
  · exact Or.inr (Or.inl cursor.2)
  · exact Or.inr (Or.inr (Or.inr (primitive_stack s shape a stack)))

private theorem primitive_writes (s : MachineData) (shape : Serialize.Desc)
    (value : SszNative.Codec.Value) (address capacity used a : BitVec 64) (retain : Bool)
    (written : Measure.Writable s
      (Serialize.measure shape value.toPrimitive (Measure.arenaState address capacity used)) a) :
    Writable s (.primitive shape)
      (SszNative.CodecMeasure.measure (.primitive shape) value
        (Measure.arenaState address capacity used) retain).effects a := by
  rw [primitive_model]
  rcases written with result | allocation | cursor | stack
  · exact Or.inl (Measure.resultWrites_span _ _ a result)
  · exact Or.inr (Or.inl ⟨_, List.mem_singleton_self _, allocation⟩)
  · exact Or.inr (Or.inr (Or.inl cursor.2))
  · exact Or.inr (Or.inr (Or.inr (primitive_stack s shape a stack)))

private theorem primitive_post {s : MachineData} {base : Int64} {shape : Serialize.Desc}
    {value : SszNative.Codec.Value} {readonly : Codec.Footprint}
    {buffer address capacity used ra : BitVec 64} {retain : Bool} {t : MachineState}
    (owned : Owned s base (.primitive shape) value readonly address capacity used ra retain)
    (old : Measure.Post s shape value.toPrimitive buffer address capacity used ra t)
    (mapping : BitVector.Mapping.Extends s.dmem t.1.dmem) :
    Post s (.primitive shape) value readonly address capacity used ra retain t := by
  have unchanged : ∀ a, readonly a → ¬ Measure.Writable s
      (Serialize.measure shape value.toPrimitive (Measure.arenaState address capacity used)) a := by
    intro a member written
    exact owned.readonlyDisjoint a member
      (primitive_writes_available s shape value address capacity used a written)
  refine {
    abi := old.abi
    observed := ?_
    active := ?_
    effects := ?_
    cursor := ?_
    usedBound := ?_
    header := old.header
    descriptor := owned.descriptor.frame old.frame unchanged
    valueStored := owned.valueStored.frame old.frame unchanged
    mapping := mapping
    frame := ?_ }
  · rw [primitive_model]
    exact (primitive_resultAt _ _ _).2 old.observed
  · rw [primitive_model]
    simp only [SszNative.CodecMeasure.primitive]
    cases result : (Serialize.measure shape value.toPrimitive
        (Measure.arenaState address capacity used)).result with
    | error reason => trivial
    | ok size =>
      change Codec.PlanAt t.1.dmem
        (ResultFootprint readonly s.regs.rdi.toBitVec
          [.primitive shape value.toPrimitive (Measure.arenaState address capacity used)
            (Serialize.measure shape value.toPrimitive (Measure.arenaState address capacity used))])
        s.regs.rdi.toBitVec (SszNative.CodecMeasure.Plan.leaf size)
      apply Codec.PlanAt.of_primitive
      · simpa only [result, Measure.ResultAt] using old.observed
      · exact ⟨owned.resultNonzero, owned.resultAligned,
          by have bound := owned.resultBound; change s.regs.rdi.toNat + 40 ≤ 2 ^ 64; omega,
          fun a inside => Or.inr (Or.inl inside)⟩
      · intro a borrowed
        have provenance := SszX86.Serialize.measure_provenance shape value.toPrimitive
          (Measure.arenaState address capacity used) a (by
            simpa only [SszX86.Serialize.ResultBorrows, result] using borrowed)
        rcases provenance with input | allocation
        · left
          cases owned.descriptor with
          | descPrimitive descriptor => exact descriptor.borrowed a input
        · exact Or.inr (Or.inr ⟨_, List.mem_singleton_self _, allocation⟩)
  · rw [primitive_model]
    intro effect member
    simp only [SszNative.CodecMeasure.primitive, List.mem_singleton] at member
    subst effect
    exact old.calls
  · rw [primitive_model]
    exact old.cursor
  · rw [primitive_model]
    exact primitive_used_bound shape value.toPrimitive
      (Measure.arenaState address capacity used) owned.usedBound
  · intro a outside
    exact old.frame a (fun written => outside
      (primitive_writes s shape value address capacity used a retain written))

/-- Original native entry-to-RET for every primitive leaf under the full recursive
ownership and return interface, preserving the complete recursive input graph even
when a compound value causes a primitive wrong-kind rejection. -/
theorem primitive_program_correct (e : Executable) (base : Int64)
    (code : CodeAt e base) (helpers : HelpersAt e base)
    (s : MachineData) (shape : Serialize.Desc) (value : SszNative.Codec.Value)
    (readonly : Codec.Footprint) (address capacity used ra : BitVec 64) (retain : Bool)
    (owned : Owned s base (.primitive shape) value readonly address capacity used ra retain) :
    Eventually (step e)
      (Post s (.primitive shape) value readonly address capacity used ra retain) (s, base) := by
  obtain ⟨buffer, primitiveOwned⟩ := owned.primitive
  have actual := Measure.program_correct e base code.primitive helpers.primitive s shape
    value.toPrimitive buffer address capacity used ra retain primitiveOwned
  apply (BitVector.Mapping.retains_mapping e _ _ actual).mono
  intro t returned
  exact primitive_post owned returned.1 returned.2

end SszX86.CodecMeasure

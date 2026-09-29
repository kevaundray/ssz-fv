import SszArm.CodecMeasurePrimitiveOwnership
import SszArm.CodecMeasurePrimitiveBacking
import SszArm.CodecLinked
import SszArm.MeasureProgram

set_option autoImplicit false

namespace SszArm.Codec.Measure

open SszNative.Codec (Value)
open SszNative.CodecMeasure (Plan)
open Delimited (MemoryFrame)

namespace Primitive

theorem allocation_writes (s : ArmState) (args : Args) (shape : SszNative.Serialize.Desc)
    (value : Value) :
    SszArm.Measure.allocationWrites args (measured s args shape value) =
      (outcome s args (.primitive shape) value).effects.flatMap (effectWrites args.arena.toNat) := by
  rw [outcome_primitive]
  rfl

theorem exact_writes_covered (s : ArmState) (args : Args) (shape : SszNative.Serialize.Desc)
    (value : Value) (low : 288 ≤ args.stack.toNat) :
    Serialize.Covers (SszArm.Measure.writesFor args (measured s args shape value))
      (writesFor args (.primitive shape) (outcome s args (.primitive shape) value)) := by
  intro span member
  rcases List.mem_append.mp member with localMember | allocationMember
  · rcases List.mem_append.mp localMember with stackMember | resultMember
    · obtain ⟨outer, member, lower, upper⟩ := stack_covered args shape _ low span stackMember
      exact ⟨outer, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl member))), lower, upper⟩
    · have extent := Serialize.resultExtent_le (measured s args shape value)
      cases result : (measured s args shape value).result with
      | ok size =>
        have same : resultWrites args (outcome s args (.primitive shape) value).result =
            SszArm.Measure.resultWrites args (measured s args shape value) := by
          rw [outcome_primitive]
          simp only [SszNative.CodecMeasure.primitive, result, Except.map, Except.mapError,
            resultWrites, SszArm.Measure.resultWrites]
        exact ⟨span, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
          (by rw [same]; exact resultMember)))), Nat.le_refl _, Nat.le_refl _⟩
      | error reason =>
        simp only [SszArm.Measure.resultWrites, result, List.mem_singleton] at resultMember
        subst span
        refine ⟨(args.result.toNat, 72), ?_, Nat.le_refl _, by dsimp; omega⟩
        apply List.mem_append.mpr
        left
        apply List.mem_append.mpr
        right
        rw [outcome_primitive]
        simp [SszNative.CodecMeasure.primitive, result, resultWrites]
  · rw [allocation_writes] at allocationMember
    exact ⟨span, List.mem_append.mpr (Or.inr allocationMember), Nat.le_refl _, Nat.le_refl _⟩

theorem post_of_legacy {s t : ArmState} {shape : SszNative.Serialize.Desc} {value : Value}
    (owned : Owned s (Args.ofEntry s) (.primitive shape) value)
    (post : SszArm.Measure.Post s t shape value.toPrimitive) :
    Post s t (.primitive shape) value ∧
      MemoryFrame (envelope s (Args.ofEntry s) (.primitive shape)) s t := by
  have low : 288 ≤ (Args.ofEntry s).stack.toNat := owned.stackLow
  have broad := Serialize.frame_of_covers post.frame
    (writes_covered s (Args.ofEntry s) shape value low)
  have returned : Delimited.Returned s t :=
    ⟨post.returned.pc, post.returned.error, post.returned.sp,
      fun reg lo hi => post.returned.registers reg (by omega) hi, post.returned.vectors⟩
  refine ⟨⟨returned, post.returned.program, ?_, ?_, post.header, ?_, ?_, ?_, ?_⟩, broad⟩
  · rw [outcome_primitive]
    apply primitive_result_at t (Args.ofEntry s).result.toNat
      (measured s (Args.ofEntry s) shape value).result
    · rcases owned.result with ⟨positive, aligned, bounded, _⟩
      exact ⟨positive, aligned, by omega, by decide⟩
    · intro size success
      apply measure_backing shape value.toPrimitive (arenaOf s (Args.ofEntry s)) _ size success
      exact descriptor_backing owned.descriptor
    · exact post.result
  · rw [outcome_primitive]
    exact post.cursor
  · intro effect member
    rw [outcome_primitive] at member
    simp only [SszNative.CodecMeasure.primitive, List.mem_singleton] at member
    subst effect
    exact post.written
  · exact Serialize.frame_of_covers post.frame
      (exact_writes_covered s (Args.ofEntry s) shape value low)
  · exact Storage.desc_at (Storage.desc_preserved owned.descriptor broad)
  · exact Storage.value_at (Storage.value_preserved owned.value_at broad)

end Primitive

/-- Original linked entry through the actual RET for the seven primitive raw
shapes, now returning the recursive Plan storage and exact effect contract.
The recursive Value input is unrestricted, including every wrong-kind branch. -/
theorem primitive_program_correct (s : ArmState) (bias : BitVec 64)
    (shape : SszNative.Serialize.Desc) (value : Value)
    (owned : Owned s (Args.ofEntry s) (.primitive shape) value)
    (code : Linked.CodeAt s bias) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = bias + 2290428#64) :
    ∃ fuel t, run fuel s = t ∧ Post s t (.primitive shape) value ∧
      MemoryFrame (envelope s (Args.ofEntry s) (.primitive shape)) s t := by
  obtain ⟨fuel, t, executed, post⟩ :=
    SszArm.Measure.program_correct s (bias + 2290428#64) shape value.toPrimitive
      owned.primitive code.legacyMeasure error aligned pc
  obtain ⟨recursivePost, broad⟩ := Primitive.post_of_legacy owned post
  exact ⟨fuel, t, executed, recursivePost, broad⟩

end SszArm.Codec.Measure

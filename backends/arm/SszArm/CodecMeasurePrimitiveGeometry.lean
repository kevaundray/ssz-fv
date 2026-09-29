import SszArm.CodecMeasureContract
import SszArm.CodecStorageLegacy
import SszArm.SerializeOwnershipMeasure
import SszArm.MeasureAllocationFacts

set_option autoImplicit false

namespace SszArm.Codec.Measure

open SszNative (NatOperand)
open SszNative.Codec (Value)
open Delimited (Span Protected)
open Serialize (Covers protected_of_covers)

namespace Primitive

abbrev measured (s : ArmState) (args : Args) (shape : SszNative.Serialize.Desc)
    (value : Value) := SszArm.Measure.outcome s args shape value.toPrimitive

theorem stack_covered (args : Args) (shape : SszNative.Serialize.Desc)
    (first : SszNative.Serialize.Outcome NatOperand) (low : 288 ≤ args.stack.toNat) :
    Covers (SszArm.Measure.stackWrites args first) (stackWrites args (.primitive shape)) := by
  intro span member
  simp only [SszArm.Measure.stackWrites, SszArm.Measure.saveWrites,
    SszArm.Measure.bodyStackWrites, List.mem_append, List.mem_singleton] at member
  refine ⟨(args.stack.toNat - 288, 288), by simp [stackWrites, stackBytes, Stack.envelope], ?_⟩
  rcases member with saved | lowering | conditional
  · subst span; dsimp; omega
  · subst span; dsimp; omega
  · split at conditional
    · simp only [List.mem_singleton] at conditional
      subst span; dsimp; omega
    · simp only [List.not_mem_nil] at conditional

theorem result_covered (args : Args) (first : SszNative.Serialize.Outcome NatOperand) :
    Covers (SszArm.Measure.resultWrites args first) [(args.result.toNat, 72)] := by
  intro span member
  have extent := Serialize.resultExtent_le first
  cases result : first.result with
  | ok size =>
    simp only [SszArm.Measure.resultWrites, result, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      refine ⟨(args.result.toNat, 72), by simp, ?_, ?_⟩ <;> dsimp <;> omega
  | error reason =>
    simp only [SszArm.Measure.resultWrites, result, List.mem_singleton] at member
    subst span
    exact ⟨_, by simp, Nat.le_refl _, by dsimp; omega⟩

theorem local_covered (args : Args) (shape : SszNative.Serialize.Desc)
    (first : SszNative.Serialize.Outcome NatOperand) (low : 288 ≤ args.stack.toNat) :
    Covers (SszArm.Measure.localWrites args first) (localEnvelope args (.primitive shape)) := by
  intro span member
  rcases List.mem_append.mp member with stack | result
  · obtain ⟨outer, member, lower, upper⟩ := stack_covered args shape first low span stack
    exact ⟨outer, List.mem_append.mpr (Or.inl member), lower, upper⟩
  · obtain ⟨outer, member, lower, upper⟩ := result_covered args first span result
    exact ⟨outer, List.mem_append.mpr (Or.inr member), lower, upper⟩

theorem writes_covered (s : ArmState) (args : Args) (shape : SszNative.Serialize.Desc)
    (value : Value) (low : 288 ≤ args.stack.toNat) :
    Covers (SszArm.Measure.writesFor args (measured s args shape value))
      (envelope s args (.primitive shape)) := by
  intro span member
  rcases List.mem_append.mp member with localMember | allocationMember
  · obtain ⟨outer, member, lower, upper⟩ :=
      local_covered args shape _ low span localMember
    exact ⟨outer, List.mem_append.mpr (Or.inl member), lower, upper⟩
  · simp only [SszArm.Measure.allocationWrites, List.mem_flatMap] at allocationMember
    obtain ⟨call, callMember, spanMember⟩ := allocationMember
    cases allocated : call.allocation with
    | none => simp only [allocated, List.not_mem_nil] at spanMember
    | some reservation =>
      simp only [allocated, List.mem_cons, List.not_mem_nil, or_false] at spanMember
      rcases spanMember with rfl | rfl
      · exact ⟨_, by simp [envelope], Nat.le_refl _, Nat.le_refl _⟩
      · have bounds := (SszArm.Measure.resource_measure (arenaOf s args) shape value.toPrimitive).allocations
          call callMember reservation allocated
        have two := SszArm.Measure.callsTwo_measure (arenaOf s args) shape value.toPrimitive
          call callMember reservation allocated
        have available : (arenaOf s args).capacity - (arenaOf s args).used ≠ 0 := by omega
        refine ⟨((arenaOf s args).base + (arenaOf s args).used,
            (arenaOf s args).capacity - (arenaOf s args).used),
          by simp [envelope, available], bounds.1, ?_⟩
        dsimp
        omega

theorem descriptor_covered (args : Args) (shape : SszNative.Serialize.Desc) :
    Covers (SszArm.Measure.descriptorSpans args shape) [(args.descriptor.toNat, 40)] := by
  intro span member
  refine ⟨(args.descriptor.toNat, 40), by simp, ?_⟩
  cases shape with
  | progressiveBitList limit =>
    cases limit <;> simp only [SszArm.Measure.descriptorSpans, List.mem_singleton] at member <;>
      subst span <;> dsimp <;> omega
  | _ =>
    simp only [SszArm.Measure.descriptorSpans, List.mem_singleton] at member
    subst span; dsimp; omega

theorem value_covered (args : Args) (value : Value) :
    Covers (SszArm.Measure.valueSpans args value.toPrimitive) [(args.value.toNat, 48)] := by
  intro span member
  refine ⟨(args.value.toNat, 48), by simp, ?_⟩
  cases value <;>
    simp only [Value.toPrimitive, SszArm.Measure.valueSpans, List.mem_cons,
      List.not_mem_nil, or_false] at member
  all_goals first
    | (subst span; dsimp; omega)
    | (rcases member with rfl | rfl <;> dsimp <;> omega)

def inputArgs (args : Args) : Emit.Args :=
  ⟨args.result, args.descriptor, args.value, 0, 0, args.stack⟩

theorem backing_eq (s : ArmState) (args : Args) (value : Value) :
    SszArm.Measure.backingSpans s args value.toPrimitive =
      Emit.backingSpan s (inputArgs args) value.toPrimitive := by
  cases value <;> rfl

end Primitive

end SszArm.Codec.Measure

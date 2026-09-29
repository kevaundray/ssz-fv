import SszArm.CodecSerializeContract

namespace SszArm.Codec.Serialize

open SszNative.Codec (Desc Value)
open Delimited (Protected)

 theorem requiredStack_min (desc : Desc) : 432 ≤ requiredStack desc := by
  have minimum := Measure.stackBytes_activation desc
  have selected := Nat.le_max_left (Measure.stackBytes desc) (Emit.stackBytes desc)
  unfold requiredStack stackBytes
  omega

 theorem requiredStack_measure (desc : Desc) : 144 + Measure.stackBytes desc ≤ requiredStack desc := by
  have selected := Nat.le_max_left (Measure.stackBytes desc) (Emit.stackBytes desc)
  unfold requiredStack stackBytes
  omega

 theorem requiredStack_emit (desc : Desc) : 144 + Emit.stackBytes desc ≤ requiredStack desc := by
  have selected := Nat.le_max_right (Measure.stackBytes desc) (Emit.stackBytes desc)
  unfold requiredStack stackBytes
  omega

 theorem measure_stack_covered (args : Args) (desc : Desc)
    (low : requiredStack desc ≤ args.stack.toNat) :
    BitVector.Covers (stackSpans args desc) (Measure.stackWrites args.measure desc) := by
  have minimum := requiredStack_min desc
  change BitVector.Covers (Stack.envelope args.stack.toNat (requiredStack desc))
    (Stack.envelope args.bodySP.toNat (Measure.stackBytes desc))
  rw [SszArm.Serialize.bodySP_toNat args (by omega)]
  exact Stack.child_cover low (requiredStack_measure desc)

 theorem measure_local_covered (args : Args) (desc : Desc)
    (low : requiredStack desc ≤ args.stack.toNat) :
    BitVector.Covers (stackSpans args desc) (Measure.localEnvelope args.measure desc) := by
  have minimum := requiredStack_min desc
  have planAddress := SszArm.Serialize.plan_toNat args (by omega)
  intro span member
  rcases List.mem_append.mp member with stack | result
  · exact measure_stack_covered args desc low span stack
  · simp only [SszArm.Serialize.Args.measure, List.mem_singleton] at result
    subst span
    refine ⟨(args.stack.toNat - requiredStack desc, requiredStack desc), by simp [stackSpans,
      Stack.envelope], ?_, ?_⟩ <;> dsimp <;> rw [planAddress] <;> omega

 theorem measure_envelope_covered (s : ArmState) (args : Args) (desc : Desc)
    (low : requiredStack desc ≤ args.stack.toNat) :
    BitVector.Covers (envelope s args desc) (Measure.envelope s args.measure desc) := by
  intro span member
  rcases List.mem_append.mp member with localMember | arena
  · obtain ⟨outer, included, lower, upper⟩ := measure_local_covered args desc low span localMember
    refine ⟨outer, ?_, lower, upper⟩
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl included)))
  · change span ∈ ((args.arena.toNat + 16, 8) ::
      (if (freeSpan s args).2 = 0 then [] else [freeSpan s args])) at arena
    exact ⟨span, List.mem_append.mpr (Or.inr arena), Nat.le_refl _, Nat.le_refl _⟩

 theorem save_covered (args : Args) (desc : Desc)
    (low : requiredStack desc ≤ args.stack.toNat) :
    BitVector.Covers (stackSpans args desc) (SszArm.Serialize.saveWrites args) := by
  have minimum := requiredStack_min desc
  exact Stack.slot_cover low (by decide : 48 ≤ 48) (by omega : 48 ≤ requiredStack desc)

 theorem measure_result_stack (args : Args) (desc : Desc)
    (low : requiredStack desc ≤ args.stack.toNat) :
    Protected (Measure.stackWrites args.measure desc) args.plan.toNat 72 := by
  have minimum := requiredStack_min desc
  have enough := requiredStack_measure desc
  have planAddress := SszArm.Serialize.plan_toNat args (by omega)
  have stackAddress := SszArm.Serialize.bodySP_toNat args (by omega)
  right
  intro span member
  simp only [Measure.stackWrites, SszArm.Serialize.Args.measure, Stack.envelope,
    List.mem_singleton] at member
  subst span
  right
  dsimp
  rw [planAddress, stackAddress]
  omega

 theorem plan_physical (args : Args) (desc : Desc)
    (low : requiredStack desc ≤ args.stack.toNat) (aligned : args.stack.toNat % 16 = 0) :
    Storage.Physical args.plan.toNat 72 8 := by
  have minimum := requiredStack_min desc
  have planAddress := SszArm.Serialize.plan_toNat args (by omega)
  have upper := args.stack.isLt
  rw [Storage.Physical, planAddress]
  exact ⟨by omega, by omega, by omega, by decide⟩

 theorem Owned.measure_descriptor {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) :
    Storage.DescOwned (Measure.envelope s args.measure desc) s args.descriptor.toNat desc :=
  Storage.Image.weaken _ (fun _ _ separated =>
    (measure_envelope_covered s args desc owned.stackLow).protected separated) owned.descriptor

 theorem Owned.measure_value {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) :
    Storage.ValueOwned (Measure.envelope s args.measure desc) s args.value.toNat value :=
  Storage.Image.weaken _ (fun _ _ separated =>
    (measure_envelope_covered s args desc owned.stackLow).protected separated) owned.value_at

end SszArm.Codec.Serialize

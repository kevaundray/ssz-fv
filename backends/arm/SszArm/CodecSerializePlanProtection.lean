import SszArm.CodecSerializeEmitGeometry
import SszArm.CodecMeasureProvenance

namespace SszArm.Codec.Serialize

open SszNative.Codec (Desc Value)
open SszNative.CodecMeasure (Plan)
open Delimited (Protected)

 theorem Owned.emit_plan_root {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (count : Nat) (fitting : count ≤ args.capacity.toNat) :
    Protected (Emit.writesFor (args.emit count) desc count) args.plan.toNat 40 := by
  have minimum := requiredStack_min desc
  have low := owned.stackLow
  have stackAddress := SszArm.Serialize.bodySP_toNat args (by omega)
  have planAddress := SszArm.Serialize.plan_toNat args (by omega)
  have childLow : Emit.stackBytes desc ≤ args.bodySP.toNat := by
    rw [stackAddress]
    exact emit_stack_low low
  have resultSeparate := (owned.resultStack.resolve_left (by decide))
    (args.stack.toNat - requiredStack desc, requiredStack desc)
    (by simp [stackSpans, Stack.envelope])
  right
  intro span member
  rcases List.mem_append.mp member with localMember | output
  · rcases List.mem_append.mp localMember with stack | result
    · simp only [Emit.stackWrites, Args.emit, Stack.envelope, List.mem_singleton] at stack
      subst span
      right
      dsimp
      rw [planAddress]
      omega
    · simp only [Emit.resultWrites, Args.emit, List.mem_cons, List.mem_singleton] at result
      rcases result with rfl | rfl <;> dsimp at resultSeparate ⊢ <;> rw [planAddress] <;> omega
  · by_cases empty : count = 0
    · simp [empty] at output
    · simp only [if_neg empty, Args.emit, List.mem_singleton] at output
      subst span
      have nonempty : args.capacity.toNat ≠ 0 := by omega
      have outputSeparate := (owned.outputStack.resolve_left nonempty)
        (args.stack.toNat - requiredStack desc, requiredStack desc)
        (by simp [stackSpans, Stack.envelope])
      dsimp at outputSeparate ⊢
      rw [planAddress]
      omega

/-- Backing ownership of the retained root is derived from original input and
arena provenance after actual measurement has produced the observed Plan. -/
theorem Owned.measured_plan {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (plan : Plan)
    (fitting : plan.size.value ≤ args.capacity.toNat)
    (success : (measured s args desc value).result = .ok plan)
    (observed : Storage.PlanAt t args.plan.toNat plan) :
    Emit.PlanOwned (Emit.writesFor (args.emit plan.size.value) desc plan.size.value)
      t args.plan (some plan) := by
  have covers := emit_envelope_covered s args desc plan.size.value owned.stackLow fitting
  have schema := Storage.Image.weaken _ (fun _ _ separated => covers.protected separated)
    owned.descriptor
  have logical := Storage.Image.weaken _ (fun _ _ separated => covers.protected separated)
    owned.value_at
  have planStored := Measure.Provenance.measured_plan_owned owned.storageBound
    (owned.emit_free_protected plan.size.value fitting) schema logical
    (owned.emit_plan_root plan.size.value fitting) success observed
  refine ⟨?_, planStored⟩
  have minimum := requiredStack_min desc
  have low := owned.stackLow
  have address := SszArm.Serialize.plan_toNat args (by omega)
  intro zero
  rw [zero] at address
  simp only [BitVec.toNat_ofNat, Nat.zero_mod] at address
  omega

end SszArm.Codec.Serialize

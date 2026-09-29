import SszArm.CodecSerializePlanProtection
import SszArm.CodecSerializeSemantics

namespace SszArm.Codec.Serialize

open SszNative.Codec (Desc Value)
open SszNative.CodecMeasure (Plan)
open Delimited (MemoryFrame)

/-- This bridge is used after the executed measurement and size guard. Its Plan
observations and byte frame are supplied by those runs, while every immutable
backing and writable separation is derived from original wrapper ownership. -/
theorem emission_owned {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (plan : Plan)
    (fitting : plan.size.value ≤ args.capacity.toNat)
    (success : (measured s args desc value).result = .ok plan)
    (observed : Storage.PlanAt t args.plan.toNat plan)
    (frame : MemoryFrame (envelope s args desc) s t) :
    Emit.Owned t (args.emit plan.size.value) desc value true plan (some plan) := by
  have capacity := emit_capacity args plan.size.value fitting
  have physical := owned.physical
  have covers := emit_envelope_covered s args desc plan.size.value owned.stackLow fitting
  refine ⟨Emit.measured_valid desc value (arenaOf s args) physical plan success,
    ?_, physical, ?_, owned.result.2.2.1, ?_, owned.emit_result_stack _, ?_, ?_,
    ?_, ?_, owned.measured_plan plan fitting success observed⟩
  · rw [capacity]
  · have minimum := requiredStack_min desc
    have low := owned.stackLow
    change Emit.stackBytes desc ≤ args.bodySP.toNat
    rw [SszArm.Serialize.bodySP_toNat args (by omega)]
    exact emit_stack_low low
  · change args.output.toNat + (args.emit plan.size.value).capacity.toNat ≤ 2^64
    rw [capacity]
    have outputBound := owned.output.2.2.1
    omega
  · simpa only [capacity] using owned.emit_output_stack plan.size.value fitting
  · simpa only [capacity] using owned.emit_output_result plan.size.value fitting
  · exact Storage.Image.weaken _ (fun _ _ separated => covers.protected separated)
      (Storage.desc_preserved owned.descriptor frame)
  · exact Storage.Image.weaken _ (fun _ _ separated => covers.protected separated)
      (Storage.value_preserved owned.value_at frame)

end SszArm.Codec.Serialize

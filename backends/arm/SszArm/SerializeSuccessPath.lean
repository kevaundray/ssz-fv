import SszArm.SerializeSuccessPathFailure
import SszArm.SerializeSuccessPathEmit

namespace SszArm.Serialize

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value)

/-- From the real measurement return, execute staging, host narrowing, the ordered
    capacity guard, the linked emitter when permitted, and the original wrapper RET.
    Every callee obligation is derived from original ownership and measurement. -/
theorem measurement_success_correct (s m : ArmState) (base : BitVec 64) (desc : Desc) (value : Value)
    (owned : Owned s (Args.ofEntry s) desc value)
    (measurement : Measured s m base desc value) (operand : NatOperand)
    (success : (measured s (Args.ofEntry s) desc value).result = .ok operand) :
    ∃ fuel t, run fuel m = t ∧ Post s t desc value := by
  obtain ⟨prepareFuel, u, prepared, ready, pc, payload⟩ :=
    SuccessPath.prepare s m base desc value owned measurement operand success
  by_cases representable : operand.value < 2^64
  · by_cases fitting : operand.value ≤ (Args.ofEntry s).capacity.toNat
    · have emitPC : read_pc u = base + 648#64 := by
        simpa only [Size.destination, representable, fitting, ↓reduceIte] using pc
      obtain ⟨fuel, t, executed, post⟩ := SuccessPath.emission_correct s u base desc value
        owned ready operand success representable fitting emitPC (payload representable)
      refine ⟨prepareFuel + fuel, t, ?_, post⟩
      rw [run_plus, prepared, executed]
    · have failurePC : read_pc u = base + BitVec.ofNat 64 Finish.Failure.capacity.entry := by
        simpa only [Size.destination, representable, fitting, ↓reduceIte,
          Finish.Failure.entry] using pc
      obtain ⟨fuel, t, executed, post⟩ := SuccessPath.failure_correct s u base desc value
        owned ready operand success .capacity failurePC (fun both => fitting both.2)
        (outcome_of_capacity_failure s (Args.ofEntry s) desc value operand success representable fitting)
      refine ⟨prepareFuel + fuel, t, ?_, post⟩
      rw [run_plus, prepared, executed]
  · have failurePC : read_pc u = base + BitVec.ofNat 64 Finish.Failure.host.entry := by
      simpa only [Size.destination, representable, ↓reduceIte, Finish.Failure.entry] using pc
    obtain ⟨fuel, t, executed, post⟩ := SuccessPath.failure_correct s u base desc value
      owned ready operand success .host failurePC (fun both => representable both.1)
      (outcome_of_host_failure s (Args.ofEntry s) desc value operand success representable)
    refine ⟨prepareFuel + fuel, t, ?_, post⟩
    rw [run_plus, prepared, executed]

end SszArm.Serialize

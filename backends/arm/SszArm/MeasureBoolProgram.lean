import SszArm.MeasureScalarBoolBody
import SszArm.MeasureActivationReturn
import SszArm.MeasureRefinement

namespace SszArm.Measure

open SszNative.Serialize (Value)

/-- The Bool descriptor starts at original PC0, includes every Value kind and
both retain flags, initializes only live fields, and reaches the actual RET. -/
theorem bool_program_correct (s : ArmState) (base : BitVec 64) (value : Value)
    (owned : Owned s (Args.ofEntry s) .bool value)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Post s t .bool value := by
  obtain ⟨entryRun, route⟩ := entry_to_body s base .bool value owned code error aligned pc
  obtain ⟨bodyFuel, t, bodyRun, produced⟩ :=
    bool_body (routed s .bool) base (Args.ofEntry s) value route.owned route.registers
      route.code route.error route.aligned (by simpa only [bodyEntry] using route.pc)
      route.descriptor route.valueTag
  obtain ⟨returnRun, post⟩ := finish_produced owned route produced
  refine ⟨11 + (dispatchOps .bool).length + bodyFuel + 7, restored t, ?_, post⟩
  rw [run_plus, run_plus, entryRun, bodyRun, returnRun]

/-- The concrete returned result observes the pinned SSZ size/error semantics. -/
theorem bool_program_refines (s : ArmState) (base : BitVec 64) (value : Value)
    (owned : Owned s (Args.ofEntry s) .bool value)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Post s t .bool value ∧
      ∃ result, ResultAt (UintCodec.widthLoad t) (Args.ofEntry s).result.toNat result ∧
        SszNative.Serialize.Measures result
          ((Ssz.serialize SszNative.Serialize.Desc.bool.erase value.erase).map Array.size) := by
  obtain ⟨fuel, t, runs, post⟩ := bool_program_correct s base value owned code error aligned pc
  exact ⟨fuel, t, runs, post, post.pinned owned.physical⟩

end SszArm.Measure

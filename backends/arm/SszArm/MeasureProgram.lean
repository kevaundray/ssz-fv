import SszArm.MeasurePrimitivePrograms
import SszArm.MeasureBitsBody

namespace SszArm.Measure

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value)

theorem bitList_program_correct (s : ArmState) (base : BitVec 64) (limit : NatOperand) (value : Value)
    (owned : Owned s (Args.ofEntry s) (.bitList limit) value)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Post s t (.bitList limit) value := by
  obtain ⟨entryRun, route⟩ := entry_to_body s base (.bitList limit) value owned code error aligned pc
  obtain ⟨bodyFuel, t, bodyRun, produced⟩ :=
    Bits.bitList_body (routed s (.bitList limit)) (Args.ofEntry s) limit value base route.owned
      route.code route.error route.aligned (by simpa only [bodyEntry] using route.pc)
      route.registers route.descriptor route.valueTag
  obtain ⟨returnRun, post⟩ := finish_produced owned route produced
  refine ⟨11 + (dispatchOps (.bitList limit)).length + bodyFuel + 7, restored t, ?_, post⟩
  rw [run_plus, run_plus, entryRun, bodyRun, returnRun]

theorem progressiveBitList_program_correct (s : ArmState) (base : BitVec 64)
    (limit : Option NatOperand) (value : Value)
    (owned : Owned s (Args.ofEntry s) (.progressiveBitList limit) value)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Post s t (.progressiveBitList limit) value := by
  obtain ⟨entryRun, route⟩ := entry_to_body s base (.progressiveBitList limit) value owned code error aligned pc
  obtain ⟨bodyFuel, t, bodyRun, produced⟩ :=
    Bits.progressiveBitList_body (routed s (.progressiveBitList limit)) (Args.ofEntry s) limit value base
      route.owned route.code route.error route.aligned (by simpa only [bodyEntry] using route.pc)
      route.registers route.descriptor route.valueTag
  obtain ⟨returnRun, post⟩ := finish_produced owned route produced
  refine ⟨11 + (dispatchOps (.progressiveBitList limit)).length + bodyFuel + 7, restored t, ?_, post⟩
  rw [run_plus, run_plus, entryRun, bodyRun, returnRun]

/-- Actual private primitive measurement, from original entry through RET. The
proof covers every value kind and both retain flags without assuming success. -/
theorem program_correct (s : ArmState) (base : BitVec 64) (desc : Desc) (value : Value)
    (owned : Owned s (Args.ofEntry s) desc value)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Post s t desc value := by
  cases desc with
  | bool => exact bool_program_correct s base value owned code error aligned pc
  | uint cap => exact uint_program_correct s base cap value owned code error aligned pc
  | byteVector cap => exact byteVector_program_correct s base cap value owned code error aligned pc
  | byteList limit => exact byteList_program_correct s base limit value owned code error aligned pc
  | bitVector cap => exact bitVector_program_correct s base cap value owned code error aligned pc
  | bitList limit => exact bitList_program_correct s base limit value owned code error aligned pc
  | progressiveBitList limit =>
    exact progressiveBitList_program_correct s base limit value owned code error aligned pc

/-- The concrete returned private Result refines the pinned SSZ serializer's
logical size/error result while Post retains the exact allocation trace and ABI. -/
theorem program_refines (s : ArmState) (base : BitVec 64) (desc : Desc) (value : Value)
    (owned : Owned s (Args.ofEntry s) desc value)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Post s t desc value ∧
      ∃ result, ResultAt (UintCodec.widthLoad t) (Args.ofEntry s).result.toNat result ∧
        SszNative.Serialize.Measures result ((Ssz.serialize desc.erase value.erase).map Array.size) := by
  obtain ⟨fuel, t, executed, post⟩ := program_correct s base desc value owned code error aligned pc
  exact ⟨fuel, t, executed, post, post.pinned owned.physical⟩

end SszArm.Measure

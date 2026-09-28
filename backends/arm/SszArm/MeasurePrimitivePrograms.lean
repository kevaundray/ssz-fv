import SszArm.MeasureBoolProgram
import SszArm.MeasureScalar
import SszArm.MeasureUintBody
import SszArm.MeasureBitVectorBody

namespace SszArm.Measure

open SszNative (NatOperand)
open SszNative.Serialize (Value)

theorem uint_program_correct (s : ArmState) (base : BitVec 64) (cap : NatOperand) (value : Value)
    (owned : Owned s (Args.ofEntry s) (.uint cap) value)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Post s t (.uint cap) value := by
  obtain ⟨entryRun, route⟩ := entry_to_body s base (.uint cap) value owned code error aligned pc
  obtain ⟨bodyFuel, t, bodyRun, produced⟩ :=
    Uint.uint_body (routed s (.uint cap)) (Args.ofEntry s) cap value base route.owned
      route.code route.error route.aligned (by simpa only [bodyEntry] using route.pc)
      route.registers route.descriptor route.valueTag
  obtain ⟨returnRun, post⟩ := finish_produced owned route produced
  refine ⟨11 + (dispatchOps (.uint cap)).length + bodyFuel + 7, restored t, ?_, post⟩
  rw [run_plus, run_plus, entryRun, bodyRun, returnRun]

theorem byteVector_program_correct (s : ArmState) (base : BitVec 64) (cap : NatOperand) (value : Value)
    (owned : Owned s (Args.ofEntry s) (.byteVector cap) value)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Post s t (.byteVector cap) value := by
  obtain ⟨entryRun, route⟩ := entry_to_body s base (.byteVector cap) value owned code error aligned pc
  obtain ⟨bodyFuel, t, bodyRun, produced⟩ :=
    byteVector_body (routed s (.byteVector cap)) base (Args.ofEntry s) cap value route.owned route.registers
      route.code route.error route.aligned (by simpa only [bodyEntry] using route.pc)
      route.descriptor route.valueTag
  obtain ⟨returnRun, post⟩ := finish_produced owned route produced
  refine ⟨11 + (dispatchOps (.byteVector cap)).length + bodyFuel + 7, restored t, ?_, post⟩
  rw [run_plus, run_plus, entryRun, bodyRun, returnRun]

theorem byteList_program_correct (s : ArmState) (base : BitVec 64) (limit : NatOperand) (value : Value)
    (owned : Owned s (Args.ofEntry s) (.byteList limit) value)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Post s t (.byteList limit) value := by
  obtain ⟨entryRun, route⟩ := entry_to_body s base (.byteList limit) value owned code error aligned pc
  obtain ⟨bodyFuel, t, bodyRun, produced⟩ :=
    byteList_body (routed s (.byteList limit)) base (Args.ofEntry s) limit value route.owned route.registers
      route.code route.error route.aligned (by simpa only [bodyEntry] using route.pc)
      route.descriptor route.valueTag
  obtain ⟨returnRun, post⟩ := finish_produced owned route produced
  refine ⟨11 + (dispatchOps (.byteList limit)).length + bodyFuel + 7, restored t, ?_, post⟩
  rw [run_plus, run_plus, entryRun, bodyRun, returnRun]

theorem bitVector_program_correct (s : ArmState) (base : BitVec 64) (cap : NatOperand) (value : Value)
    (owned : Owned s (Args.ofEntry s) (.bitVector cap) value)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Post s t (.bitVector cap) value := by
  obtain ⟨entryRun, route⟩ := entry_to_body s base (.bitVector cap) value owned code error aligned pc
  obtain ⟨bodyFuel, t, bodyRun, produced⟩ :=
    bitVector_body (routed s (.bitVector cap)) base (Args.ofEntry s) cap value route.owned route.registers
      route.code route.error route.aligned (by simpa only [bodyEntry] using route.pc)
      route.descriptor route.valueTag
  obtain ⟨returnRun, post⟩ := finish_produced owned route produced
  refine ⟨11 + (dispatchOps (.bitVector cap)).length + bodyFuel + 7, restored t, ?_, post⟩
  rw [run_plus, run_plus, entryRun, bodyRun, returnRun]

end SszArm.Measure

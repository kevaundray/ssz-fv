import SszArm.CodecMeasureSingletonReserve
import SszArm.CodecLinkedPlanSingleton

set_option autoImplicit false

namespace SszArm.Codec.Measure.Singleton

/-- The guard proof consumes the exact words of the complete linked helper. -/
theorem code_of_linked (s : ArmState) (base : BitVec 64)
    (code : Linked.PlanSingleton.CodeAt s base) : CodeAt s base := by
  intro op
  apply Linked.PlanSingleton.chunk0_codeAt code (op.pc, op.word)
  cases op <;> decide

theorem linked_checks_runs (s : ArmState) (base address capacity used : BitVec 64)
    (code : Linked.PlanSingleton.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 12#64)
    (headerBase : read_mem_bytes 8 (r (.GPR 1) s) s = address)
    (headerCapacity : read_mem_bytes 8 (r (.GPR 1) s + 8#64) s = capacity)
    (headerUsed : read_mem_bytes 8 (r (.GPR 1) s + 16#64) s = used) :
    ∃ fuel t, run fuel s = t ∧ ChecksPost s t base address capacity used :=
  checks_runs s base address capacity used (code_of_linked s base code)
    error pc headerBase headerCapacity headerUsed

end SszArm.Codec.Measure.Singleton

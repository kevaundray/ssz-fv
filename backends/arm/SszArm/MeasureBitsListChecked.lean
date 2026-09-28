import SszArm.MeasureBitsListPrefixStep
import SszArm.MeasureBitsListCompareRuntime

namespace SszArm.Measure.Bits.List

open SszNative (NatOperand)
open SszNative.Serialize (Packed)

theorem compare_prefix_executes (schema : Schema) (s u : ArmState) (args : Args) (bits : Packed)
    (actual cap : NatOperand) (base : BitVec 64) (owned : Owned s args schema.descriptor (.bits bits))
    (pre : Prefix s u args schema bits actual) (present : schema.cap = some cap)
    (code : CodeAt u base) (error : read_err u = .None) (aligned : CheckSPAlignment u)
    (pc : read_pc u = base + 1712#64) :
    ∃ fuel t, run fuel u = t ∧ Prefix s t args schema bits actual ∧
      read_pc t = if actual.value ≤ cap.value then base + 1852#64 else base + 1744#64 := by
  have stackLow : 16 ≤ (r (.GPR 31#5) u).toNat := by
    have low := owned.stackLow
    rw [pre.core.stack, Args.bodySP]
    bv_omega
  have capRegisters : r (.GPR 22#5) u = cap.pointer ∧ r (.GPR 23#5) u = cap.payload := by
    simpa only [present] using pre.core.cap
  obtain ⟨fuel, t, executed, compared⟩ := ListEntry.compare_executes u base actual cap
    code error aligned pc stackLow pre.core.pointer pre.core.payload capRegisters.1 capRegisters.2
    pre.actualAt (Prefix.cap_at owned pre cap present)
    (Prefix.actual_lower_owned owned pre) (Prefix.cap_lower_owned owned pre cap present)
  have core := pre.core.of_registers (by
    intro reg member
    apply compared.registers reg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have next := Prefix.lower_step owned pre core compared.program (compared.error.trans error.symm)
    compared.frame (by
      intro reg member
      apply compared.registers reg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide) compared.vectors
  exact ⟨fuel, t, executed, next, compared.pc⟩

end SszArm.Measure.Bits.List

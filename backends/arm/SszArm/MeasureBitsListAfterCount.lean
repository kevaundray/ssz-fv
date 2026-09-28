import SszArm.MeasureBitsListSelected
import SszArm.MeasureBitsListChecked
import SszArm.MeasureBitsListLimit
import SszArm.MeasureBitsListWidthBody

namespace SszArm.Measure.Bits.List

open SszNative (NatOperand)
open SszNative.Serialize (Packed)

theorem after_count_executes (schema : Schema) (s u : ArmState) (args : Args) (bits : Packed)
    (actual : NatOperand) (base : BitVec 64) (owned : Owned s args schema.descriptor (.bits bits))
    (counted : CountPost s u args schema bits base actual) (code : CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment u) :
    ∃ fuel t, run fuel u = t ∧ Produced s t args schema.descriptor (.bits bits) base := by
  obtain ⟨selectFuel, v, selectedRun, pre, selectedPC⟩ := selected_executes schema s u args bits actual base
    owned counted (code.congr counted.program) (counted.error.trans error) aligned
  have vSP : r (.GPR 31#5) v = r (.GPR 31#5) u := pre.core.stack.trans counted.work.stack.symm
  have vAligned : CheckSPAlignment v := by
    simpa only [CheckSPAlignment, state_simp_rules, vSP] using aligned
  cases present : schema.cap with
  | none =>
    have checked : (SszNative.Serialize.bounded schema.cap actual (countCall s args bits).used).result = .ok () := by
      simp only [present, SszNative.Serialize.bounded, SszNative.Serialize.unchanged]
    have pc : read_pc v = base + 1852#64 := by simpa only [present, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] using selectedPC
    obtain ⟨fuel, t, executed, post⟩ := width_executes schema s v args bits actual base owned pre checked
      (code.congr pre.program) (pre.error.trans error) vAligned pc
    exact ⟨selectFuel + fuel, t, by rw [run_plus, selectedRun, executed], post⟩
  | some cap =>
    have pc : read_pc v = base + 1712#64 := by simpa only [present, Option.isSome_some, ↓reduceIte] using selectedPC
    obtain ⟨compareFuel, w, compareRun, compared, comparePC⟩ := compare_prefix_executes schema s v args bits
      actual cap base owned pre present (code.congr pre.program) (pre.error.trans error) vAligned pc
    have wSP : r (.GPR 31#5) w = r (.GPR 31#5) u := compared.core.stack.trans counted.work.stack.symm
    have wAligned : CheckSPAlignment w := by
      simpa only [CheckSPAlignment, state_simp_rules, wSP] using aligned
    by_cases fits : actual.value ≤ cap.value
    · have checked : (SszNative.Serialize.bounded schema.cap actual (countCall s args bits).used).result = .ok () := by
        simp only [present, SszNative.Serialize.bounded, fits, ↓reduceIte, SszNative.Serialize.unchanged]
      have pc : read_pc w = base + 1852#64 := by simpa only [fits, ↓reduceIte] using comparePC
      obtain ⟨fuel, t, executed, post⟩ := width_executes schema s w args bits actual base owned compared checked
        (code.congr compared.program) (compared.error.trans error) wAligned pc
      exact ⟨(selectFuel + compareFuel) + fuel, t,
        by rw [run_plus, run_plus, selectedRun, compareRun, executed], post⟩
    · have pc : read_pc w = base + 1744#64 := by simpa only [fits, ↓reduceIte] using comparePC
      obtain ⟨t, executed, post⟩ := limit_executes schema s w args bits actual cap base owned compared present fits
        (code.congr compared.program) (compared.error.trans error) wAligned pc
      exact ⟨(selectFuel + compareFuel) + 29, t,
        by rw [run_plus, run_plus, selectedRun, compareRun, executed], post⟩

end SszArm.Measure.Bits.List

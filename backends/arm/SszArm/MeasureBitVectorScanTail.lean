import SszArm.MeasureBitVectorScanLoad
import SszArm.MeasureBitVectorScanTailSteps

namespace SszArm.Measure.BitVector

open Result

def scanTailOps : List Op := [p632, p636, p640]

@[irreducible] def scanTailResult (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (if r (.GPR 14#5) s = 0#64 then base + 592#64 else base + 644#64)
    (w (.GPR 13#5) (r (.GPR 13#5) s - 1#64) (w (.GPR 12#5) (r (.GPR 13#5) s) s))

theorem scan_tail_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 632#64) : run 3 s = scanTailResult s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base scanTailOps s := by
    simp (config := {decide := true, instances := true})
      [scanTailOps, Follows, show p632.offset = 632 by rfl, show p636.offset = 636 by rfl,
       show p640.offset = 640 by rfl, scan_remember_effect, scan_decrement_effect,
       state_simp_rules, bitvec_rules, minimal_theory, pc, error, BitVec.add_assoc]
  rw [show 3 = scanTailOps.length by rfl, runs _ s base code follows]
  change p640.effect (p636.effect (p632.effect s)) = scanTailResult s base
  rw [scan_limb_branch_effect, scan_decrement_effect, scan_remember_effect]
  by_cases zero : r (.GPR 14#5) s = 0#64 <;>
    simp (config := {decide := true, instances := true})
      [scanTailResult, state_simp_rules, bitvec_rules, minimal_theory, pc, zero,
       BitVec.add_assoc, NatExact.gpr_w_pc, w_of_w_shadow]

theorem scan_tail_frame (s : ArmState) (base : BitVec 64) : ScanFrame s (scanTailResult s base) := by
  constructor
  · simp [scanTailResult, state_simp_rules]
  · simp [scanTailResult, state_simp_rules]
  · intro reg outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    simp (disch := simp_all) [scanTailResult, state_simp_rules]
  · intro reg
    simp [scanTailResult, state_simp_rules]
  · intro address outside
    simp [scanTailResult, state_simp_rules]

end SszArm.Measure.BitVector

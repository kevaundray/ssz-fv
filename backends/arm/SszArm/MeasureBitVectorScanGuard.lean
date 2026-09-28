import SszArm.MeasureBitVectorFrame
import SszArm.MeasureBitVectorBranchSteps

namespace SszArm.Measure.BitVector

open Result

def scanGuardOps : List Op := [p592, p596]

@[irreducible] def scanGuardResult (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + BitVec.ofNat 64
    (if r (.GPR 13#5) s + 1#64 = 0#64 then 2828 else 600))
    (write_pstate (AddWithCarry (r (.GPR 13#5) s) 1#64 0#1).2 s)

theorem scan_guard_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 592#64) : run 2 s = scanGuardResult s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base scanGuardOps s := by
    simp (config := {decide := true, instances := true})
      [scanGuardOps, Follows, show p592.offset = 592 by rfl, show p596.offset = 596 by rfl,
       scan_count_effect, state_simp_rules, bitvec_rules, minimal_theory,
       pc, error, BitVec.add_assoc]
  rw [show 2 = scanGuardOps.length by rfl, runs _ s base code follows]
  change p596.effect (p592.effect s) = scanGuardResult s base
  rw [scan_zero_branch_effect, scan_count_effect]
  by_cases zero : r (.GPR 13#5) s + 1#64 = 0#64 <;>
    simp (config := {decide := true, instances := true})
      [scanGuardResult, state_simp_rules, bitvec_rules, minimal_theory, pc,
       BitVec.add_assoc, NatCompare.count_zero_bit, zero]

theorem scan_guard_frame (s : ArmState) (base : BitVec 64) :
    ScanFrame s (scanGuardResult s base) := by
  constructor
  · simp [scanGuardResult, state_simp_rules]
  · simp [scanGuardResult, state_simp_rules]
  · intro reg outside
    simp [scanGuardResult, state_simp_rules]
  · intro reg
    simp [scanGuardResult, state_simp_rules]
  · intro address outside
    simp [scanGuardResult, state_simp_rules]

@[simp] theorem scan_guard_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (scanGuardResult s base) = r (.GPR reg) s := by
  simp [scanGuardResult, state_simp_rules]

end SszArm.Measure.BitVector

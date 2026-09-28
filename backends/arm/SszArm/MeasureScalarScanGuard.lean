import SszArm.MeasureScalarScanLoad

namespace SszArm.Measure.Scalar.Bytes

open Result

def Kind.guardOps : Kind → List Op
  | .vector => [p1180, p1184]
  | .list => [p820, p824]

@[irreducible] def scanGuardResult (kind : Kind) (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + BitVec.ofNat 64
    (if r (.GPR 11#5) s + 1#64 = 0#64 then kind.scanZero else kind.scanLoad))
    (write_pstate (AddWithCarry (r (.GPR 11#5) s) 1#64 0#1).2 s)

theorem scan_guard_run (kind : Kind) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.scanGuard) :
    run 2 s = scanGuardResult kind s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base kind.guardOps s := by
    cases kind <;>
      simp (config := {decide := true, instances := true})
        [Kind.guardOps, Kind.scanGuard, Follows, p1180, p1184, p820, p824,
         Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         pc, error, BitVec.add_assoc]
  rw [show 2 = kind.guardOps.length by cases kind <;> rfl, runs _ s base code follows]
  cases kind <;>
    simp (config := {decide := true, instances := true})
      [scanGuardResult, Kind.scanGuard, Kind.scanZero, Kind.scanLoad, Kind.guardOps,
       effect, p1180, p1184, p820, p824, Op.effect, exec_inst, state_simp_rules,
       bitvec_rules, minimal_theory, pc, BitVec.add_assoc, NatCompare.count_zero_bit]
  all_goals split
  all_goals
    apply state_eq_iff_components_eq.mpr
    refine ⟨?_, ?_, ?_⟩
    · intro field
      cases field <;> simp [state_simp_rules]
      all_goals cases ‹PFlag› <;> simp [state_simp_rules]
    · simp [state_simp_rules]
    · intro bytes address
      simp [state_simp_rules]

theorem scan_guard_frame (kind : Kind) (s : ArmState) (base : BitVec 64) :
    NatNarrow.Frame s (scanGuardResult kind s base) := by
  constructor
  · simp [scanGuardResult, state_simp_rules]
  · simp [scanGuardResult, state_simp_rules]
  · intro reg outside; simp [scanGuardResult, state_simp_rules]
  · intro reg; simp [scanGuardResult, state_simp_rules]
  · intro address outside; simp [scanGuardResult, state_simp_rules]

@[simp] theorem scan_guard_register (kind : Kind) (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (scanGuardResult kind s base) = r (.GPR reg) s := by
  simp [scanGuardResult, state_simp_rules]

end SszArm.Measure.Scalar.Bytes

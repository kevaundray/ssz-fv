import SszArm.MeasureScalarScanGuard

namespace SszArm.Measure.Scalar.Bytes

open Result

def Kind.tailOps : Kind → List Op
  | .vector => [p1220, p1224, p1228]
  | .list => [p860, p864]

@[irreducible] def scanTailResult (kind : Kind) (s : ArmState) (base : BitVec 64) : ArmState :=
  let u := match kind with
    | .vector => w (.GPR 10#5) (r (.GPR 11#5) s) s
    | .list => s
  w .PC (base + BitVec.ofNat 64
    (if r (.GPR 12#5) s = 0#64 then kind.scanGuard else kind.scanExit))
    (w (.GPR 11#5) (r (.GPR 11#5) s - 1#64) u)

theorem scan_tail_run (kind : Kind) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.scanTail) :
    run kind.tailOps.length s = scanTailResult kind s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base kind.tailOps s := by
    cases kind <;>
      simp (config := {decide := true, instances := true})
        [Kind.tailOps, Kind.scanTail, Follows, p1220, p1224, p1228, p860, p864,
         Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         pc, error, BitVec.add_assoc]
  rw [runs _ s base code follows]
  cases kind <;>
    simp (config := {decide := true, instances := true})
      [scanTailResult, Kind.scanTail, Kind.scanGuard, Kind.scanExit, Kind.tailOps,
       effect, p1220, p1224, p1228, p860, p864, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, pc, BitVec.add_assoc,
       NatExact.gpr_w_pc, w_of_w_shadow]
  all_goals split <;> simp_all

theorem scan_tail_frame (kind : Kind) (s : ArmState) (base : BitVec 64) :
    NatNarrow.Frame s (scanTailResult kind s base) := by
  constructor
  · cases kind <;> simp [scanTailResult, state_simp_rules]
  · cases kind <;> simp [scanTailResult, state_simp_rules]
  · intro reg outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    cases kind <;> simp (disch := simp_all) [scanTailResult, state_simp_rules]
  · intro reg; cases kind <;> simp [scanTailResult, state_simp_rules]
  · intro address outside; cases kind <;> simp [scanTailResult, state_simp_rules]

end SszArm.Measure.Scalar.Bytes

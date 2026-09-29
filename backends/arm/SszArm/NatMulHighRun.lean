import SszArm.NatMulHigh

namespace SszArm.NatMul

inductive HighPhase where
  | save | digits | lowCross | highCross | combine | restore
  deriving DecidableEq

def HighPhase.ops : HighPhase → List Op
  | .save => highSaveOps | .digits => highCore0 | .lowCross => highCore1
  | .highCross => highCore2 | .combine => highCore3 | .restore => highRestoreOps

def HighPhase.start : HighPhase → Nat
  | .save => 760 | .digits => 788 | .lowCross => 804
  | .highCross => 816 | .combine => 832 | .restore => 844

theorem high_phase_run (phase : HighPhase) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 phase.start) :
    run phase.ops.length s = block base phase.ops s := by
  apply block_run base phase.ops s code error aligned
  have hpc : r .PC s = base + BitVec.ofNat 64 phase.start := pc
  cases phase <;> simp [HighPhase.ops, HighPhase.start, highSaveOps, highCore0,
    highCore1, highCore2, highCore3, highRestoreOps, Follows, Op.row, Op.effect,
    put, next, state_simp_rules, hpc, BitVec.add_assoc]

theorem high_phase_pc (phase : HighPhase) (s : ArmState) (base : BitVec 64) :
    read_pc (block base phase.ops s) = read_pc s + BitVec.ofNat 64 (4 * phase.ops.length) := by
  apply NatMulStateFold.advancing (fun t op => op.effect base t) phase.ops s
  intro op member t
  cases phase <;>
    simp only [HighPhase.ops, highSaveOps, highCore0, highCore1, highCore2, highCore3,
      highRestoreOps, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Op.effect, put, next, state_simp_rules]

theorem high_save_pc (s : ArmState) (base : BitVec 64) :
    read_pc (block base highSaveOps s) = read_pc s + 28#64 :=
  high_phase_pc .save s base

theorem high_core_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 788#64) :
    run 14 s = block base highCoreOps s := by
  let a := block base highCore0 s
  let b := block base highCore1 a
  let c := block base highCore2 b
  have aCode : CodeAt a base := by simpa only [a, CodeAt, block_program] using code
  have aError : read_err a = .None := (block_error _ _ _).trans error
  have aAligned : CheckSPAlignment a := block_aligned _ _ _ aligned
  have aPC : read_pc a = base + 804#64 := by
    rw [show a = block base HighPhase.digits.ops s from rfl, high_phase_pc, pc]
    simp [HighPhase.ops, highCore0, BitVec.add_assoc]
  have bCode : CodeAt b base := by simpa only [b, CodeAt, block_program] using aCode
  have bError : read_err b = .None := (block_error _ _ _).trans aError
  have bAligned : CheckSPAlignment b := block_aligned _ _ _ aAligned
  have bPC : read_pc b = base + 816#64 := by
    rw [show b = block base HighPhase.lowCross.ops a from rfl, high_phase_pc, aPC]
    simp [HighPhase.ops, highCore1, BitVec.add_assoc]
  have cCode : CodeAt c base := by simpa only [c, CodeAt, block_program] using bCode
  have cError : read_err c = .None := (block_error _ _ _).trans bError
  have cAligned : CheckSPAlignment c := block_aligned _ _ _ bAligned
  have cPC : read_pc c = base + 832#64 := by
    rw [show c = block base HighPhase.highCross.ops b from rfl, high_phase_pc, bPC]
    simp [HighPhase.ops, highCore2, BitVec.add_assoc]
  have first : run 4 s = a := high_phase_run .digits s base code error aligned pc
  have second : run 3 a = b := high_phase_run .lowCross a base aCode aError aAligned aPC
  have third : run 4 b = c := high_phase_run .highCross b base bCode bError bAligned bPC
  have fourth : run 3 c = block base highCore3 c :=
    high_phase_run .combine c base cCode cError cAligned cPC
  change run (4 + (3 + (4 + 3))) s = _
  rw [high_core_split, run_plus, first, run_plus, second, run_plus, third]
  exact fourth

def highCompleted (s : ArmState) (base : BitVec 64) : ArmState :=
  block base highRestoreOps (block base highCoreOps (block base highSaveOps s))

theorem high_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 760#64) :
    run 28 s = highCompleted s base := by
  let a := block base highSaveOps s
  let b := block base highCoreOps a
  have aCode : CodeAt a base := by simpa only [a, CodeAt, block_program] using code
  have aError : read_err a = .None := (block_error _ _ _).trans error
  have aAligned : CheckSPAlignment a := block_aligned _ _ _ aligned
  have aPC : read_pc a = base + 788#64 := by
    rw [show a = block base highSaveOps s from rfl, high_save_pc, pc]
    simp [BitVec.add_assoc]
  have bCode : CodeAt b base := by simpa only [b, CodeAt, block_program] using aCode
  have bError : read_err b = .None := (block_error _ _ _).trans aError
  have bAligned : CheckSPAlignment b := block_aligned _ _ _ aAligned
  have bPC : read_pc b = base + 844#64 := by
    rw [show b = block base highCoreOps a from rfl, high_core_pc, aPC]
    simp [BitVec.add_assoc]
  have save : run 7 s = a := high_phase_run .save s base code error aligned pc
  have core : run 14 a = b := high_core_run a base aCode aError aAligned aPC
  have restore : run 7 b = highCompleted s base :=
    high_phase_run .restore b base bCode bError bAligned bPC
  change run (7 + (14 + 7)) s = _
  rw [run_plus, save, run_plus, core]
  exact restore

theorem high_completed_pc (s : ArmState) (base : BitVec 64) :
    read_pc (highCompleted s base) = read_pc s + 112#64 := by
  unfold highCompleted
  rw [show highRestoreOps = HighPhase.restore.ops from rfl, high_phase_pc,
    high_core_pc, high_save_pc]
  simp [HighPhase.ops, highRestoreOps, BitVec.add_assoc]

theorem high_completed_value (s : ArmState) (base : BitVec 64) :
    r (.GPR 18#5) (highCompleted s base) =
      NatMulProduct.high (r (.GPR 18#5) s) (r (.GPR 14#5) s) := by
  have restore : ∀ t, r (.GPR 18#5) (block base highRestoreOps t) = r (.GPR 18#5) t := by
    intro t
    simp [highRestoreOps, block, Op.effect, put, next, state_simp_rules]
  rw [highCompleted, restore, high_core_value, high_save_effect]
  simp [highSpilled, state_simp_rules]

end SszArm.NatMul

import SszArm.NatMulWordHigh
import SszArm.WordNormalize

namespace SszArm.NatMulWord

def highCompleted (site : HighSite) (s : ArmState) (base : BitVec 64) : ArmState :=
  block base site.restoreOps (block base site.coreOps (block base site.saveOps s))

theorem high_save_pc (site : HighSite) (s : ArmState) (base : BitVec 64) :
    read_pc (block base site.saveOps s) = read_pc s + 28#64 := by
  rw [high_save_effect] <;> arm_state_nf

theorem high_save_run (site : HighSite) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 site.start) :
    run 7 s = block base site.saveOps s := by
  have hpc : r .PC s = base + BitVec.ofNat 64 site.start := pc
  rw [show 7 = site.saveOps.length by cases site <;> rfl]
  apply block_run base site.saveOps s code error aligned
  cases site <;> simp [HighSite.saveOps, HighSite.start, Follows, Op.row, Op.effect,
    put, next, state_simp_rules, hpc, BitVec.add_assoc]

theorem high_core_run (site : HighSite) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (site.start + 28)) :
    run 14 s = block base site.coreOps s := by
  have hpc : r .PC s = base + BitVec.ofNat 64 (site.start + 28) := pc
  rw [show 14 = site.coreOps.length by cases site <;> rfl]
  apply block_run base site.coreOps s code error aligned
  cases site <;> simp [HighSite.coreOps, HighSite.start, Follows, Op.row, Op.effect,
    put, next, state_simp_rules, hpc, BitVec.add_assoc]

theorem high_restore_run (site : HighSite) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (site.start + 84)) :
    run 7 s = block base site.restoreOps s := by
  have hpc : r .PC s = base + BitVec.ofNat 64 (site.start + 84) := pc
  rw [show 7 = site.restoreOps.length by cases site <;> rfl]
  apply block_run base site.restoreOps s code error aligned
  cases site <;> simp [HighSite.restoreOps, HighSite.start, Follows, Op.row, Op.effect,
    put, next, state_simp_rules, hpc, BitVec.add_assoc]

theorem high_run (site : HighSite) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 site.start) :
    run 28 s = highCompleted site s base := by
  let a := block base site.saveOps s
  let b := block base site.coreOps a
  have aCode : CodeAt a base := by simpa only [a, CodeAt, block_program] using code
  have aError : read_err a = .None := (block_error _ _ _).trans error
  have aAligned : CheckSPAlignment a := block_aligned _ _ _ aligned
  have aPC : read_pc a = base + BitVec.ofNat 64 (site.start + 28) := by
    rw [show a = block base site.saveOps s from rfl, high_save_pc, pc]
    simp [BitVec.ofNat_add, BitVec.add_assoc]
  have bCode : CodeAt b base := by simpa only [b, CodeAt, block_program] using aCode
  have bError : read_err b = .None := (block_error _ _ _).trans aError
  have bAligned : CheckSPAlignment b := block_aligned _ _ _ aAligned
  have bPC : read_pc b = base + BitVec.ofNat 64 (site.start + 84) := by
    rw [show b = block base site.coreOps a from rfl, high_core_pc, aPC]
    simp [BitVec.ofNat_add, BitVec.add_assoc]
  change run (7 + (14 + 7)) s = _
  rw [run_plus, high_save_run site s base code error aligned pc, run_plus,
    high_core_run site a base aCode aError aAligned aPC,
    high_restore_run site b base bCode bError bAligned bPC]
  rfl

theorem high_completed_pc (site : HighSite) (s : ArmState) (base : BitVec 64) :
    read_pc (highCompleted site s base) = read_pc s + 112#64 := by
  unfold highCompleted
  have restore : ∀ t, read_pc (block base site.restoreOps t) = read_pc t + 28#64 := by
    intro t
    have length : site.restoreOps.length = 7 := by cases site <;> rfl
    rw [show 28#64 = BitVec.ofNat 64 (4 * site.restoreOps.length) by rw [length]]
    refine NatMulStateFold.advancing (fun u (op : Op) => op.effect base u)
      site.restoreOps t ?_
    intro op member u
    cases site <;>
      simp only [HighSite.restoreOps, List.mem_cons, List.not_mem_nil, or_false] at member
    all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Op.effect, put, next, state_simp_rules]
  rw [restore, high_core_pc, high_save_pc]
  simp [BitVec.add_assoc]

theorem high_save_registers (site : HighSite) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (notSP : reg ≠ 31#5) :
    r (.GPR reg) (block base site.saveOps s) = r (.GPR reg) s := by
  have stackField : StateField.GPR reg ≠ .GPR 31#5 :=
    fun equal => notSP (StateField.GPR.inj equal)
  have pcField : StateField.GPR reg ≠ .PC := by
    intro equal
    cases equal
  rw [high_save_effect, r_of_w_different stackField, r_of_w_different pcField] <;>
    simp only [HighSite.spilled, NatMulSpill.six, r_of_write_mem_bytes]

theorem high_completed_value (site : HighSite) (s : ArmState) (base : BitVec 64) :
    r (.GPR site.destination) (highCompleted site s base) =
      NatMulProduct.high (r (.GPR site.left) s) (r (.GPR 3#5) s) := by
  have restore : ∀ t, r (.GPR site.destination) (block base site.restoreOps t) =
      r (.GPR site.destination) t := by
    intro t
    refine NatMulStateFold.preserves (fun u (op : Op) => op.effect base u)
      (fun u => r (.GPR site.destination) u) site.restoreOps t ?_
    intro op member u
    cases site <;>
      simp only [HighSite.restoreOps, List.mem_cons, List.not_mem_nil, or_false] at member
    all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [HighSite.destination, Op.effect, put, next, state_simp_rules]
  unfold highCompleted
  rw [restore, high_core_value,
    high_save_registers site s base site.left (by cases site <;> decide),
    high_save_registers site s base 3#5 (by decide)]

end SszArm.NatMulWord

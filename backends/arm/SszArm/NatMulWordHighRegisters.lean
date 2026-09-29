import SszArm.NatMulWordHighRun
import SszArm.WordNormalize

namespace SszArm.NatMulWord

theorem high_core_registers (site : HighSite) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (notSaved : reg ∉ site.saved) (notDestination : reg ≠ site.destination) :
    r (.GPR reg) (block base site.coreOps s) = r (.GPR reg) s := by
  have pcField : StateField.GPR reg ≠ .PC := by
    intro equal
    cases equal
  refine NatMulStateFold.preserves (fun t (op : Op) => op.effect base t)
    (fun t => r (.GPR reg) t) site.coreOps s ?_
  intro op member t
  cases site <;>
    simp only [HighSite.coreOps, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [HighSite.saved, HighSite.destination] at notSaved notDestination
    simp only [Op.effect, put, next]
    arm_word_nf at notSaved notDestination
    arm_state_nf <;> simp_all

theorem high_restore_registers (site : HighSite) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (notSaved : reg ∉ site.saved) (notSP : reg ≠ 31#5) :
    r (.GPR reg) (block base site.restoreOps s) = r (.GPR reg) s := by
  have pcField : StateField.GPR reg ≠ .PC := by
    intro equal
    cases equal
  refine NatMulStateFold.preserves (fun t (op : Op) => op.effect base t)
    (fun t => r (.GPR reg) t) site.restoreOps s ?_
  intro op member t
  cases site <;>
    simp only [HighSite.restoreOps, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [HighSite.saved] at notSaved
    simp only [Op.effect, put, next]
    arm_word_nf at notSaved notSP
    arm_state_nf <;> simp_all

end SszArm.NatMulWord

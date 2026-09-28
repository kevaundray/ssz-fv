import SszArm.NatMulWordHighSave

namespace SszArm.NatMulWord

theorem high_core_value (site : HighSite) (s : ArmState) (base : BitVec 64) :
    r (.GPR site.destination) (block base site.coreOps s) =
      NatMulProduct.high (r (.GPR site.left) s) (r (.GPR 3#5) s) := by
  let a := block base site.core0 s
  let b := block base site.core1 a
  have digit := high_digits site s base
  have low := high_low_cross site a base
  have upper := high_high_cross site b base
  have a1b : r (.GPR site.a1) b = r (.GPR site.a1) a :=
    high_low_cross_preserved site a base site.a1 (by cases site <;> decide)
  have b1b : r (.GPR site.b1) b = r (.GPR site.b1) a :=
    high_low_cross_preserved site a base site.b1 (by cases site <;> decide)
  have a0b : r (.GPR site.a0) b = r (.GPR site.a0) a :=
    high_low_cross_preserved site a base site.a0 (by cases site <;> decide)
  rw [high_core_split, high_combine,
    high_high_cross_preserved site b base site.a1 (by cases site <;> decide) (by cases site <;> decide),
    high_high_cross_preserved site b base site.b1 (by cases site <;> decide) (by cases site <;> decide),
    upper.1, upper.2, a1b, b1b, a0b, low, digit.1, digit.2.1, digit.2.2.1, digit.2.2.2]
  rfl

theorem high_core_mem (site : HighSite) (s : ArmState) (base : BitVec 64) :
    (block base site.coreOps s).mem = s.mem := by
  apply NatMulStateFold.preserves (fun t op => op.effect base t) ArmState.mem site.coreOps s
  intro op member t
  cases site <;> simp only [HighSite.coreOps, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Op.effect, put, next, state_simp_rules]

theorem high_core_sp (site : HighSite) (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (block base site.coreOps s) = r (.GPR 31#5) s := by
  apply NatMulStateFold.preserves (fun t op => op.effect base t) (r (.GPR 31#5)) site.coreOps s
  intro op member t
  cases site <;> simp only [HighSite.coreOps, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Op.effect, put, next, state_simp_rules]

theorem high_core_pc (site : HighSite) (s : ArmState) (base : BitVec 64) :
    read_pc (block base site.coreOps s) = read_pc s + 56#64 := by
  have length : site.coreOps.length = 14 := by cases site <;> rfl
  rw [show 56#64 = BitVec.ofNat 64 (4 * site.coreOps.length) by rw [length]]
  apply NatMulStateFold.advancing (fun t op => op.effect base t) site.coreOps s
  intro op member t
  cases site <;> simp only [HighSite.coreOps, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Op.effect, put, next, state_simp_rules]

end SszArm.NatMulWord

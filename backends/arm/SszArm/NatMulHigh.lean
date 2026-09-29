import SszArm.NatMulHighStages

namespace SszArm.NatMul

theorem high_save_effect (s : ArmState) (base : BitVec 64) :
    block base highSaveOps s =
      w (.GPR 31#5) (r (.GPR 31#5) s - 48#64)
        (w .PC (read_pc s + 28#64) (highSpilled s)) := by
  rw [high_save_word]
  exact NatMulWord.high_save_effect .first s base

theorem high_core_mem (s : ArmState) (base : BitVec 64) :
    (block base highCoreOps s).mem = s.mem := by
  apply NatMulStateFold.preserves (fun t op => op.effect base t) ArmState.mem highCoreOps s
  intro op member t
  simp only [highCoreOps, highCore0, highCore1, highCore2, highCore3,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Op.effect, put, next, state_simp_rules]

theorem high_core_registers (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (notSaved : reg ∉ highSaved) (notDestination : reg ≠ 18#5) :
    r (.GPR reg) (block base highCoreOps s) = r (.GPR reg) s := by
  apply NatMulStateFold.preserves (fun t op => op.effect base t) (r (.GPR reg)) highCoreOps s
  intro op member t
  simp only [highCoreOps, highCore0, highCore1, highCore2, highCore3,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all (config := {decide := true}) [highSaved, Op.effect, put, next, state_simp_rules]

theorem high_core_sp (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (block base highCoreOps s) = r (.GPR 31#5) s :=
  high_core_registers s base _ (by decide) (by decide)

theorem high_core_pc (s : ArmState) (base : BitVec 64) :
    read_pc (block base highCoreOps s) = read_pc s + 56#64 := by
  change read_pc (block base highCoreOps s) =
    read_pc s + BitVec.ofNat 64 (4 * highCoreOps.length)
  apply NatMulStateFold.advancing (fun t op => op.effect base t) highCoreOps s
  intro op member t
  simp only [highCoreOps, highCore0, highCore1, highCore2, highCore3,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Op.effect, put, next, state_simp_rules]

theorem high_core_flags (s : ArmState) (base : BitVec 64) (flag : PFlag) :
    r (.FLAG flag) (block base highCoreOps s) = r (.FLAG flag) s := by
  apply NatMulStateFold.preserves (fun t op => op.effect base t) (r (.FLAG flag)) highCoreOps s
  intro op member t
  simp only [highCoreOps, highCore0, highCore1, highCore2, highCore3,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Op.effect, put, next, state_simp_rules]

end SszArm.NatMul

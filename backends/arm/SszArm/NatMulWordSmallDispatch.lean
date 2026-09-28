import SszArm.NatMulWordSmallMemory

namespace SszArm.NatMulWord

/-- PC1040 computes the low product; PC1044 tests the restored high product. -/
def smallDispatch (s : ArmState) (base : BitVec 64) : ArmState :=
  block base [.p1040, .p1044] s

theorem small_dispatch_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1040#64) : run 2 s = smallDispatch s base := by
  have hpc : r .PC s = base + 1040#64 := pc
  apply block_run base [.p1040, .p1044] s code error aligned
  simp [Follows, Op.row, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]

theorem small_dispatch_pc (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 1040#64) :
    read_pc (smallDispatch s base) =
      if r (.GPR 9#5) s = 0#64 then base + 1048#64 else base + 1132#64 := by
  have hpc : r .PC s = base + 1040#64 := pc
  simp [smallDispatch, block, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]

theorem small_dispatch_low (s : ArmState) (base : BitVec 64) :
    r (.GPR 8#5) (smallDispatch s base) = r (.GPR 2#5) s * r (.GPR 3#5) s := by
  simp [smallDispatch, block, Op.effect, put, next, state_simp_rules]

theorem small_dispatch_high (s : ArmState) (base : BitVec 64) :
    r (.GPR 9#5) (smallDispatch s base) = r (.GPR 9#5) s := by
  simp [smallDispatch, block, Op.effect, put, next, state_simp_rules]

theorem small_dispatch_frame (s : ArmState) (base : BitVec 64) :
    SmallFrame s (smallDispatch s base) := by
  refine ⟨⟨block_program _ _ _, block_error _ _ _, ?_, ?_⟩, ?_⟩
  · intro reg keep
    have different : reg ≠ 8#5 := by
      simp_all only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    simp [smallDispatch, block, Op.effect, put, next, state_simp_rules, different]
  · intro reg
    simp [smallDispatch, block, Op.effect, put, next, state_simp_rules]
  · intro a _
    simp [smallDispatch, block, Op.effect, put, next, state_simp_rules]

end SszArm.NatMulWord

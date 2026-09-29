import SszArm.NatMulDispatchTail

namespace SszArm.NatMul

theorem left_zero_guard_pc (s : ArmState) (base : BitVec 64) :
    read_pc (block base [.p212] s) =
      base + (if r (.GPR 21#5) s = 0#64 then 264#64 else 216#64) := by
  simp only [block, List.foldl_cons, List.foldl_nil, Op.effect]
  arm_state_nf
  all_goals simp [apply_ite]

theorem left_zero_guard_registers (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (block base [.p212] s) = r (.GPR reg) s := by
  simp only [block, List.foldl_cons, List.foldl_nil, Op.effect, NatCompare.r_gpr_of_w_pc]

/-- The left-zero guard runs before the shared right-count comparison. -/
theorem right_count_follows (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 212#64) (nonzero : r (.GPR 21#5) s ≠ 0#64) :
    Follows base [.p212, .p216, .p220] s := by
  refine ⟨hp, count_branch_follows (Op.p212.effect base s) base false ?_⟩
  have pc : read_pc (Op.p212.effect base s) =
      base + (if r (.GPR 21#5) s = 0#64 then 264#64 else 216#64) := left_zero_guard_pc s base
  simpa only [nonzero, ↓reduceIte, countBranchStart, Bool.false_eq_true] using pc

theorem right_count_registers (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (block base [.p212, .p216, .p220] s) = r (.GPR reg) s :=
  (count_branch_registers (block base [.p212] s) base false reg).trans
    (left_zero_guard_registers s base reg)

theorem right_count_pc (s : ArmState) (base : BitVec 64) :
    read_pc (block base [.p212, .p216, .p220] s) =
      base + (if r (.GPR 22#5) s = 1#64 then 224#64 else 376#64) := by
  have pc : read_pc (block base [.p212, .p216, .p220] s) =
      base + (if r (.GPR 22#5) (block base [.p212] s) = 1#64 then 224#64 else 376#64) :=
    count_branch_pc (block base [.p212] s) base false
  exact pc.trans (congrArg (fun word : BitVec 64 =>
    base + (if word = 1#64 then 224#64 else 376#64)) (left_zero_guard_registers s base 22#5))

theorem right_one_load_values (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 224#64) :
    let t := block base [.p224] s
    read_pc t = base + 228#64 ∧
    r (.GPR 1#5) t = r (.GPR 1#5) s ∧
    r (.GPR 2#5) t = r (.GPR 2#5) s ∧
    r (.GPR 3#5) t = r (.GPR 3#5) s ∧
    r (.GPR 4#5) t = read_mem_bytes 8 (r (.GPR 3#5) s) s := by
  have hpc : r .PC s = base + 224#64 := hp
  simp only [block, List.foldl_cons, List.foldl_nil, Op.effect, put, next]
  arm_state_nf
  all_goals simp [hpc, BitVec.add_assoc]

end SszArm.NatMul

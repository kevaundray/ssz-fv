import SszArm.NatMulDispatchFrame

namespace SszArm.NatMul

def countBranchOps (left : Bool) : List Op :=
  if left then [.p376, .p380] else [.p216, .p220]

def countBranchReg (left : Bool) : BitVec 5 := if left then 21#5 else 22#5

def countBranchStart (left : Bool) : BitVec 64 := if left then 376#64 else 216#64

def countBranchOne (left : Bool) : BitVec 64 := if left then 384#64 else 224#64

def countBranchMany (left : Bool) : BitVec 64 := if left then 412#64 else 376#64

theorem count_branch_follows (s : ArmState) (base : BitVec 64) (left : Bool)
    (hp : read_pc s = base + countBranchStart left) :
    Follows base (countBranchOps left) s := by
  have hpc : r .PC s = base + countBranchStart left := hp
  cases left
  all_goals
    simp only [countBranchOps, Bool.false_eq_true, ↓reduceIte, Follows, Op.row,
      Op.effect, Udivti3.compare, Udivti3.next, write_pstate]
    arm_state_nf
  all_goals simp [hpc, countBranchStart, BitVec.add_assoc]

/-- CMP and its conditional branch preserve every scalar, including scan X9. -/
theorem count_branch_registers (s : ArmState) (base : BitVec 64) (left : Bool) (reg : BitVec 5) :
    r (.GPR reg) (block base (countBranchOps left) s) = r (.GPR reg) s := by
  have flagDifferent (flag : PFlag) : StateField.GPR reg ≠ StateField.FLAG flag := by
    intro equality
    cases equality
  cases left
  all_goals
    simp only [countBranchOps, Bool.false_eq_true, ↓reduceIte, block,
      List.foldl_cons, List.foldl_nil, Op.effect, Udivti3.compare, Udivti3.next, write_pstate]
    arm_state_nf
  all_goals simp only [NatCompare.r_gpr_of_w_pc,
    r_of_w_different (flagDifferent .N), r_of_w_different (flagDifferent .Z),
    r_of_w_different (flagDifferent .C), r_of_w_different (flagDifferent .V)]

theorem count_branch_pc (s : ArmState) (base : BitVec 64) (left : Bool) :
    read_pc (block base (countBranchOps left) s) =
      base + (if r (.GPR (countBranchReg left)) s = 1#64 then
        countBranchOne left else countBranchMany left) := by
  cases left
  all_goals
    simp only [countBranchOps, countBranchReg, countBranchOne, countBranchMany,
      Bool.false_eq_true, ↓reduceIte, block, List.foldl_cons, List.foldl_nil,
      Op.effect, Udivti3.compare, Udivti3.next, write_pstate]
    arm_state_nf
  all_goals simp [Udivti3.cmp_zero, ite_not, apply_ite]

end SszArm.NatMul

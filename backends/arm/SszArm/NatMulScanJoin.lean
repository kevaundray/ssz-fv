import SszArm.NatMulScanJoinState

namespace SszArm.NatMul

theorem left_join_allowed (zero : Bool) (right : BitVec 64) :
    ∀ op ∈ leftJoinOps zero right, op ∈ scanPureOps := by
  cases zero <;> by_cases small : right = 0#64 <;>
    simp only [leftJoinOps, small, Bool.false_eq_true, ↓reduceIte]
  all_goals decide

theorem left_join_follows (s : ArmState) (base : BitVec 64) (zero : Bool)
    (hp : read_pc s = base + (if zero then 124#64 else 88#64)) :
    Follows base (leftJoinOps zero (r (.GPR 3#5) s)) s := by
  have hpc : r .PC s = base + (if zero then 124#64 else 88#64) := hp
  cases zero <;> by_cases small : r (.GPR 3#5) s = 0#64
  all_goals
    arm_word_nf at small hpc
    simp only [leftJoinOps, small, Bool.false_eq_true, ↓reduceIte, Follows,
      Op.row, Op.effect, put, next, read_pc]
    arm_state_nf
  all_goals simp [small, hpc, BitVec.add_assoc]

theorem left_join_count (s : ArmState) (base : BitVec 64) (zero : Bool) :
    r (.GPR 21#5) (block base (leftJoinOps zero (r (.GPR 3#5) s)) s) =
      if zero then 0#64 else r (.GPR 10#5) s + 1#64 := by
  rw [left_join_result]
  simp only [leftJoinResult]
  arm_state_nf

theorem left_join_index (s : ArmState) (base : BitVec 64) (zero : Bool) :
    r (.GPR 9#5) (block base (leftJoinOps zero (r (.GPR 3#5) s)) s) = r (.GPR 9#5) s := by
  rw [left_join_result]
  simp only [leftJoinResult]
  arm_state_nf

theorem left_join_raw (s : ArmState) (base : BitVec 64) (zero : Bool) :
    r (.GPR 8#5) (block base (leftJoinOps zero (r (.GPR 3#5) s)) s) = r (.GPR 2#5) s := by
  rw [left_join_result]
  simp only [leftJoinResult]
  arm_state_nf

theorem left_join_pc (s : ArmState) (base : BitVec 64) (zero : Bool) :
    read_pc (block base (leftJoinOps zero (r (.GPR 3#5) s)) s) =
      base + (if r (.GPR 3#5) s = 0#64 then 136#64 else 160#64) := by
  rw [left_join_result]
  simp only [leftJoinResult]
  arm_state_nf

end SszArm.NatMul

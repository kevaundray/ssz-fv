import SszArm.NatAddWidth
import SszArm.NatAddArithmetic

namespace SszArm.NatAdd

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

inductive WidthPath where
  | largeRight | smallRight
  deriving DecidableEq

def WidthPath.start : WidthPath → Nat
  | .largeRight => 360 | .smallRight => 108

def WidthPath.ops : WidthPath → List Op
  | .largeRight => [.p360, .p364, .p368, .p372, .p376, .p380]
  | .smallRight => [.p108, .p112, .p116, .p120, .p124]

/-- The same unsigned width classifier handles the borrowed and immediate right
representations. The representation bit in X9 is not a canonicality premise. -/
theorem width_select (s : ArmState) (base : BitVec 64) (path : WidthPath)
    (leftCount rightCount : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 path.start)
    (leftPositive : 0 < leftCount) (rightPositive : 0 < rightCount)
    (leftBound : leftCount < 2^64) (rightBound : rightCount < 2^64)
    (leftReg : r (.GPR 8#5) s = BitVec.ofNat 64 leftCount)
    (rightReg : match path with
      | .largeRight => r (.GPR 10#5) s = BitVec.ofNat 64 (rightCount - 1)
      | .smallRight => rightCount = 1) :
    let t := block base path.ops s
    run path.ops.length s = t ∧ NatCompare.Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      r (.GPR 8#5) t = BitVec.ofNat 64 leftCount ∧
      r (.GPR 10#5) t = BitVec.ofNat 64 rightCount ∧
      r (.GPR 9#5) t = (if path = .largeRight then 1#64 else 0#64) ∧
      read_pc t = base + (if leftCount ≤ 1 ∧ rightCount ≤ 1 then 384#64 else 128#64) := by
  have notZero : BitVec.ofNat 64 leftCount ≠ 0#64 := by bv_omega
  have increment : BitVec.ofNat 64 (rightCount - 1) + 1#64 = BitVec.ofNat 64 rightCount := by
    bv_omega
  have widthGuard : ((BitVec.ofNat 64 leftCount) ||| (BitVec.ofNat 64 rightCount)).toNat < 2 ↔
      leftCount ≤ 1 ∧ rightCount ≤ 1 := by
    rw [width_or_small]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt leftBound, Nat.mod_eq_of_lt rightBound]
  have hpc : r .PC s = base + BitVec.ofNat 64 path.start := hp
  have follow : Follows base path.ops s := by
    cases path <;>
      simp_all [WidthPath.start, WidthPath.ops, Follows, Op.row, Op.effect, put, next,
        Udivti3.compare, Udivti3.next, state_simp_rules, BitVec.add_assoc]
  refine ⟨block_run base path.ops s hc he ha follow,
    scan_frame base _ _ (by cases path <;> decide),
    scan_zero base _ _ (by cases path <;> decide), ?_, ?_, ?_, ?_⟩
  · cases path <;> simp [WidthPath.ops, block, Op.effect, put, next,
      Udivti3.compare, Udivti3.next, state_simp_rules, leftReg]
  · cases path <;> simp_all [WidthPath.ops, block, Op.effect, put, next,
      Udivti3.compare, Udivti3.next, state_simp_rules]
  · cases path <;> simp [WidthPath.ops, block, Op.effect, put, next,
      Udivti3.compare, Udivti3.next, state_simp_rules]
  · have carryGuard : (AddWithCarry
        (BitVec.ofNat 64 leftCount ||| BitVec.ofNat 64 rightCount) (~~~(2#64)) 1#1).2.c = 1#1 ↔
        ¬ (leftCount ≤ 1 ∧ rightCount ≤ 1) := by
      rw [Udivti3.cmp_carry]
      simp only [BitVec.toNat_ofNat]
      omega
    cases path <;> by_cases small : leftCount ≤ 1 ∧ rightCount ≤ 1 <;>
      simp_all [WidthPath.ops, block, Op.effect, put, next, Udivti3.compare,
        Udivti3.next, state_simp_rules]

end SszArm.NatAdd

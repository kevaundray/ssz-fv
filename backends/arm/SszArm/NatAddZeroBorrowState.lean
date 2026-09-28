import SszArm.NatAddZeroOwned

namespace SszArm.NatAdd

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def borrowValuePath (right : Bool) : StatusPath := if right then .right else .left

def borrowNormalOps (right : Bool) (one : Bool) : List Op :=
  (if right then [.p472, .p476, .p480] else [.p636, .p640, .p644]) ++
    if one then (if right then [.p484, .p488] else [.p648, .p652]) else []

def borrowNormalState (right one : Bool) (base : BitVec 64) (s : ArmState) : ArmState :=
  block base (borrowNormalOps right one) s

theorem borrow_normal_frame (right one : Bool) (base : BitVec 64) (s : ArmState) :
    ZeroFrame s (borrowNormalState right one base s) := by
  constructor
  · exact block_program base _ s
  · exact block_error base _ s
  · cases right <;> cases one <;>
      simp [borrowNormalState, borrowNormalOps, block, Op.effect, put, next,
        Udivti3.compare, Udivti3.next, state_simp_rules]
  · cases right <;> cases one <;>
      simp [borrowNormalState, borrowNormalOps, block, Op.effect, put, next,
        Udivti3.compare, Udivti3.next, state_simp_rules]
  · intro reg low high
    have h1 : reg ≠ 1#5 := by bv_omega
    have h2 : reg ≠ 2#5 := by bv_omega
    have h3 : reg ≠ 3#5 := by bv_omega
    have h4 : reg ≠ 4#5 := by bv_omega
    cases right <;> cases one <;>
      simp [borrowNormalState, borrowNormalOps, block, Op.effect, put, next,
        Udivti3.compare, Udivti3.next, state_simp_rules, h1, h2, h3, h4]
  · intro reg low high
    cases right <;> cases one <;>
      simp [borrowNormalState, borrowNormalOps, block, Op.effect, put, next,
        Udivti3.compare, Udivti3.next, state_simp_rules]
  · intro a outside
    cases right <;> cases one <;>
      simp [borrowNormalState, borrowNormalOps, block, Op.effect, put, next,
        Udivti3.compare, Udivti3.next, state_simp_rules]

/-- The actual collapse/descriptor block observed without any image, execution,
or ownership hypotheses. Its source memory premise is only the first physical word. -/
theorem borrow_normal_observations (right : Bool) (s : ArmState)
    (base pointer word : BitVec 64) (n : Nat)
    (hp : r .PC s = base + BitVec.ofNat 64 (if right then 472 else 636))
    (ptr : r (.GPR (borrowPointer right)) s = pointer)
    (positive : 0 < n) (bound : n < 2^64)
    (count : r (.GPR 8#5) s = BitVec.ofNat 64 (n - 1))
    (low : read_mem_bytes 8 pointer s = word) :
    let one := decide (n = 1)
    let t := borrowNormalState right one base s
    Follows base (borrowNormalOps right one) s ∧
      read_pc t = base + BitVec.ofNat 64 (valueStart (borrowValuePath right)) ∧
      valuePointer (borrowValuePath right) t = (if n = 1 then 0#64 else pointer) ∧
      valuePayload (borrowValuePath right) t = (if n = 1 then word else BitVec.ofNat 64 n) := by
  have increment : BitVec.ofNat 64 (n - 1) + 1#64 = BitVec.ofNat 64 n := by bv_omega
  have guard : (AddWithCarry (BitVec.ofNat 64 n) (~~~(1#64)) 1#1).2.z = 1#1 ↔
      n = 1 := by
    rw [Udivti3.cmp_zero]
    bv_omega
  have eqone : BitVec.ofNat 64 n = 1#64 ↔ n = 1 := by bv_omega
  cases right <;> simp [borrowPointer] at ptr
  all_goals
    by_cases one : n = 1 <;>
      simp [borrowNormalState, borrowNormalOps, borrowValuePath, borrowPointer,
        valueStart, valuePointer, valuePayload, Follows, Op.row, block, Op.effect,
        put, next, Udivti3.compare, Udivti3.next, state_simp_rules, hp, ptr,
        count, increment, guard, eqone, one, low, BitVec.add_assoc]

end SszArm.NatAdd

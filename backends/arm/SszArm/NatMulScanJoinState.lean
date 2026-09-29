import SszArm.NatMulScanStages

namespace SszArm.NatMul

def leftJoinOps (zero : Bool) (right : BitVec 64) : List Op :=
  if zero then [.p124, .p128, .p132]
  else if right = 0#64 then [.p88, .p92, .p96, .p100] else [.p88, .p92, .p96]

/-- Algebraic join checkpoint; the original source and count registers remain
opaque when later scalar observations use this summary. -/
def leftJoinResult (s : ArmState) (base count : BitVec 64) : ArmState :=
  w .PC (base + (if r (.GPR 3#5) s = 0#64 then 136#64 else 160#64))
    (w (.GPR 8#5) (r (.GPR 2#5) s) (w (.GPR 21#5) count s))

theorem left_zero_join_result (s : ArmState) (base : BitVec 64) :
    block base [.p124, .p128, .p132] s = leftJoinResult s base 0#64 := by
  simp only [block, List.foldl_cons, List.foldl_nil, Op.effect, put, next, leftJoinResult]
  arm_state_nf
  all_goals simp [apply_ite]

theorem left_small_join_result (s : ArmState) (base : BitVec 64)
    (small : r (.GPR 3#5) s = 0#64) :
    block base [.p88, .p92, .p96, .p100] s =
      leftJoinResult s base (r (.GPR 10#5) s + 1#64) := by
  arm_word_nf at small
  simp only [block, List.foldl_cons, List.foldl_nil, Op.effect, put, next, leftJoinResult]
  arm_state_nf
  all_goals simp [small]

theorem left_large_join_result (s : ArmState) (base : BitVec 64)
    (large : r (.GPR 3#5) s ≠ 0#64) :
    block base [.p88, .p92, .p96] s =
      leftJoinResult s base (r (.GPR 10#5) s + 1#64) := by
  arm_word_nf at large
  simp only [block, List.foldl_cons, List.foldl_nil, Op.effect, put, next, leftJoinResult]
  arm_state_nf
  all_goals simp [large]

theorem left_join_result (s : ArmState) (base : BitVec 64) (zero : Bool) :
    block base (leftJoinOps zero (r (.GPR 3#5) s)) s =
      leftJoinResult s base (if zero then 0#64 else r (.GPR 10#5) s + 1#64) := by
  cases zero with
  | true => exact left_zero_join_result s base
  | false =>
    by_cases small : r (.GPR 3#5) s = 0#64
    · simpa only [leftJoinOps, Bool.false_eq_true, ↓reduceIte, small] using
        left_small_join_result s base small
    · simpa only [leftJoinOps, Bool.false_eq_true, ↓reduceIte, small] using
        left_large_join_result s base small

end SszArm.NatMul

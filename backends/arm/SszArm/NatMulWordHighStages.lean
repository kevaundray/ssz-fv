import SszArm.NatMulWordHighOps
import SszArm.NatMulStateFold

namespace SszArm.NatMulWord

theorem high_put_gpr (destination reg : BitVec 5) (value : BitVec 64) (s : ArmState) :
    r (.GPR reg) (put destination value s) =
      if reg = destination then value else r (.GPR reg) s := by
  by_cases same : reg = destination
  · subst reg
    simp [put, next, state_simp_rules]
  · simp [put, next, state_simp_rules, same]

def HighSite.a0 : HighSite → BitVec 5
  | .first => 9#5
  | .loop => 9#5
  | .small => 10#5

def HighSite.a1 : HighSite → BitVec 5
  | .first => 10#5
  | .loop => 10#5
  | .small => 11#5

def HighSite.b0 : HighSite → BitVec 5
  | .first => 11#5
  | .loop => 11#5
  | .small => 12#5

def HighSite.b1 : HighSite → BitVec 5
  | .first => 12#5
  | .loop => 12#5
  | .small => 13#5

def HighSite.v : HighSite → BitVec 5
  | .first => 13#5
  | .loop => 13#5
  | .small => 14#5

def HighSite.z : HighSite → BitVec 5
  | .first => 15#5
  | .loop => 14#5
  | .small => 15#5

def HighSite.core0 : HighSite → List Op
  | .first => [.p508, .p512, .p516, .p520]
  | .loop => [.p664, .p668, .p672, .p676]
  | .small => [.p956, .p960, .p964, .p968]

def HighSite.core1 : HighSite → List Op
  | .first => [.p524, .p528, .p532]
  | .loop => [.p680, .p684, .p688]
  | .small => [.p972, .p976, .p980]

def HighSite.core2 : HighSite → List Op
  | .first => [.p536, .p540, .p544, .p548]
  | .loop => [.p692, .p696, .p700, .p704]
  | .small => [.p984, .p988, .p992, .p996]

def HighSite.core3 : HighSite → List Op
  | .first => [.p552, .p556, .p560]
  | .loop => [.p708, .p712, .p716]
  | .small => [.p1000, .p1004, .p1008]

theorem high_core_split (site : HighSite) (s : ArmState) (base : BitVec 64) :
    block base site.coreOps s = block base site.core3
      (block base site.core2 (block base site.core1 (block base site.core0 s))) := by
  have ops : site.coreOps = site.core0 ++ site.core1 ++ site.core2 ++ site.core3 := by
    cases site <;> rfl
  simp only [block, ops, List.foldl_append]

theorem high_digits (site : HighSite) (s : ArmState) (base : BitVec 64) :
    r (.GPR site.a0) (block base site.core0 s) = ((r (.GPR site.left) s).setWidth 32).setWidth 64 ∧
    r (.GPR site.a1) (block base site.core0 s) = r (.GPR site.left) s >>> 32 ∧
    r (.GPR site.b0) (block base site.core0 s) = ((r (.GPR 3#5) s).setWidth 32).setWidth 64 ∧
    r (.GPR site.b1) (block base site.core0 s) = r (.GPR 3#5) s >>> 32 := by
  cases site <;>
    simp (config := {decide := true}) only [HighSite.core0, HighSite.a0, HighSite.a1,
      HighSite.b0, HighSite.b1, HighSite.left, block, List.foldl_cons, List.foldl_nil,
      Op.effect, high_put_gpr, ↓reduceIte]

theorem high_low_cross (site : HighSite) (s : ArmState) (base : BitVec 64) :
    r (.GPR site.v) (block base site.core1 s) =
      r (.GPR site.a1) s * r (.GPR site.b0) s +
        ((r (.GPR site.a0) s * r (.GPR site.b0) s) >>> 32) := by
  cases site <;>
    simp (config := {decide := true}) only [HighSite.core1, HighSite.a0, HighSite.a1,
      HighSite.b0, HighSite.v, block, List.foldl_cons, List.foldl_nil, Op.effect,
      high_put_gpr, ↓reduceIte]
  all_goals exact BitVec.add_comm _ _

theorem high_low_cross_preserved (site : HighSite) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (different : reg ≠ site.v) :
    r (.GPR reg) (block base site.core1 s) = r (.GPR reg) s := by
  refine NatMulStateFold.preserves (fun t (op : Op) => op.effect base t)
    (fun t => r (.GPR reg) t) site.core1 s ?_
  intro op member t
  cases site <;> simp only [HighSite.core1, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl | rfl
  all_goals
    simp only [Op.effect, high_put_gpr]
    split
    next same => exact False.elim (different (by with_unfolding_all exact same))
    next _ => rfl

theorem high_high_cross (site : HighSite) (s : ArmState) (base : BitVec 64) :
    r (.GPR site.b0) (block base site.core2 s) = r (.GPR site.v) s >>> 32 ∧
    r (.GPR site.z) (block base site.core2 s) =
      (r (.GPR site.a0) s * r (.GPR site.b1) s +
        ((r (.GPR site.v) s).setWidth 32).setWidth 64) >>> 32 := by
  cases site <;>
    simp (config := {decide := true}) only [HighSite.core2, HighSite.a0, HighSite.b0,
      HighSite.b1, HighSite.v, HighSite.z, block, List.foldl_cons, List.foldl_nil,
      Op.effect, high_put_gpr, ↓reduceIte, true_and]
  all_goals congr 1; exact BitVec.add_comm _ _

theorem high_high_cross_preserved (site : HighSite) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (notHigh : reg ≠ site.b0) (notCross : reg ≠ site.z) :
    r (.GPR reg) (block base site.core2 s) = r (.GPR reg) s := by
  refine NatMulStateFold.preserves (fun t (op : Op) => op.effect base t)
    (fun t => r (.GPR reg) t) site.core2 s ?_
  intro op member t
  cases site <;> simp only [HighSite.core2, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl
  all_goals
    simp only [Op.effect, high_put_gpr]
    split
    next same =>
      exact False.elim (by
        first
        | exact notHigh (by with_unfolding_all exact same)
        | exact notCross (by with_unfolding_all exact same))
    next _ => rfl

theorem high_combine (site : HighSite) (s : ArmState) (base : BitVec 64) :
    r (.GPR site.destination) (block base site.core3 s) =
      r (.GPR site.a1) s * r (.GPR site.b1) s + r (.GPR site.b0) s + r (.GPR site.z) s := by
  cases site <;>
    simp (config := {decide := true}) only [HighSite.core3, HighSite.a1, HighSite.b0,
      HighSite.b1, HighSite.v, HighSite.z, HighSite.destination, block,
      List.foldl_cons, List.foldl_nil, Op.effect, high_put_gpr, ↓reduceIte]
  all_goals congr 1; exact BitVec.add_comm _ _

end SszArm.NatMulWord

import SszArm.NatAddBlocks

namespace SszArm.NatAdd

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

inductive SumPath where
  | immediate | normalized
  deriving DecidableEq

def SumPath.start : SumPath → Nat
  | .immediate => 544 | .normalized => 980

def SumPath.ops (path : SumPath) (overflow : Bool) : List Op :=
  match path with
  | .immediate => [.p544, .p548] ++
      (if overflow then [.p560] else [.p552, .p556]) ++ [.p564] ++
      (if overflow then [.p568] else [])
  | .normalized => [.p980, .p984] ++
      (if overflow then [.p996] else [.p988, .p992]) ++ [.p1000]

def sumOverflow (a b : BitVec 64) : Bool := decide (2^64 ≤ a.toNat + b.toNat)

theorem sum_carry (a b : BitVec 64) :
    (AddWithCarry a b 0#1).2.c = 1#1 ↔ 2^64 ≤ a.toNat + b.toNat := by
  simpa only [Udivti3.radix, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero]
    using Udivti3.adc_carry a b 0#1

/-- Pure control observations, separate from image binding and execution. -/
theorem one_word_follows (s : ArmState) (base : BitVec 64) (path : SumPath)
    (a b : BitVec 64)
    (hp : r .PC s = base + BitVec.ofNat 64 path.start)
    (h2 : r (.GPR 2#5) s = a) (h4 : r (.GPR 4#5) s = b)
    (h8 : path = .normalized → r (.GPR 8#5) s = 0#64) :
    Follows base (path.ops (sumOverflow a b)) s := by
  by_cases overflow : 2^64 ≤ a.toNat + b.toNat <;> cases path <;>
    simp [SumPath.start] at hp
  all_goals
    simp [SumPath.ops, sumOverflow, overflow, Follows, Op.row,
      Op.effect, put, next, state_simp_rules, hp, h2, h4, h8,
      sum_carry, BitVec.add_assoc]

theorem one_word_fields (s : ArmState) (base : BitVec 64) (path : SumPath)
    (a b : BitVec 64)
    (h2 : r (.GPR 2#5) s = a) (h4 : r (.GPR 4#5) s = b)
    (h8 : path = .normalized → r (.GPR 8#5) s = 0#64) :
    let t := block base (path.ops (sumOverflow a b)) s
    r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      r (.GPR 9#5) t = a + b ∧
      r (.GPR 8#5) t = (if 2^64 ≤ a.toNat + b.toNat then 1#64 else 0#64) ∧
      read_pc t = base + (if 2^64 ≤ a.toNat + b.toNat then 1112#64 else 1004#64) := by
  by_cases overflow : 2^64 ≤ a.toNat + b.toNat <;> cases path <;>
    simp [SumPath.ops, sumOverflow, overflow, block, Op.effect, put, next,
      state_simp_rules, h2, h4, h8, sum_carry]

/-- Carry flags and caller-saved work registers do not change the comparison
frame; this observation is independent of all arithmetic preconditions. -/
theorem one_word_frame (s : ArmState) (base : BitVec 64)
    (path : SumPath) (overflow : Bool) :
    NatCompare.Frame s (block base (path.ops overflow) s) := by
  cases path <;> cases overflow
  all_goals
    constructor
    · simp [SumPath.ops, block, Op.effect, put, next, state_simp_rules]
    · simp [SumPath.ops, block, Op.effect, put, next, state_simp_rules]
    · intro reg hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp (disch := simp_all) [SumPath.ops, block, Op.effect, put, next,
        state_simp_rules]
    · intro reg
      simp [SumPath.ops, block, Op.effect, put, next, state_simp_rules]
    · intro address outside
      simp [SumPath.ops, block, Op.effect, put, next, state_simp_rules]

end SszArm.NatAdd

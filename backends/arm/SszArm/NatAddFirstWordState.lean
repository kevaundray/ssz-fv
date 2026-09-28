import SszArm.NatAddOneWordState

namespace SszArm.NatAdd

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

inductive FirstKind where
  | largeLarge | largeSmall | smallLarge
  deriving DecidableEq

def FirstKind.ops (kind : FirstKind) (overflow : Bool) : List Op :=
  [.p276] ++
    (if kind = .smallLarge then [.p1448, .p1452, .p1456, .p1460]
     else [.p280, .p284, .p288, .p1468]) ++
    (if kind = .largeSmall then
      [.p1488, .p1492, .p1496] ++
        (if overflow then [.p1508] else [.p1500, .p1504]) ++ [.p1512, .p1516]
     else (if kind = .largeLarge then [.p1472] else []) ++
      [.p1476, .p1480, .p1484, .p1524, .p1528] ++
        (if overflow then [.p1540] else [.p1532, .p1536]) ++ [.p1544, .p1548] ++
        (if kind = .largeLarge then [.p1552] else [])) ++
    (if kind = .smallLarge then [] else [.p1556, .p1560, .p1564, .p1568])

/-- Control follows only the operand tags, nonempty large operands, and ADD carry. -/
theorem first_word_follows (s : ArmState) (base a b : BitVec 64) (kind : FirstKind)
    (hp : r .PC s = base + 276#64)
    (leftKind : r (.GPR 1#5) s = 0#64 ↔ kind = .smallLarge)
    (rightKind : r (.GPR 3#5) s = 0#64 ↔ kind = .largeSmall)
    (left : if kind = .smallLarge then r (.GPR 2#5) s = a else
      r (.GPR 2#5) s ≠ 0#64 ∧ read_mem_bytes 8 (r (.GPR 1#5) s) s = a)
    (right : if kind = .largeSmall then r (.GPR 4#5) s = b else
      r (.GPR 4#5) s ≠ 0#64 ∧ read_mem_bytes 8 (r (.GPR 3#5) s) s = b) :
    Follows base (kind.ops (sumOverflow a b)) s := by
  cases kind <;> simp at leftKind rightKind left right
  all_goals
    by_cases overflow : 2^64 ≤ a.toNat + b.toNat <;>
      simp [FirstKind.ops, sumOverflow, overflow, Follows, Op.row, Op.effect,
        put, next, state_simp_rules, hp, leftKind, rightKind, left, right,
        sum_carry, BitVec.add_assoc]

/-- Exact final work-register observations, without execution or image hypotheses. -/
theorem first_word_fields (s : ArmState) (base a b : BitVec 64) (kind : FirstKind)
    (leftKind : r (.GPR 1#5) s = 0#64 ↔ kind = .smallLarge)
    (left : if kind = .smallLarge then r (.GPR 2#5) s = a else
      r (.GPR 2#5) s ≠ 0#64 ∧ read_mem_bytes 8 (r (.GPR 1#5) s) s = a)
    (right : if kind = .largeSmall then r (.GPR 4#5) s = b else
      r (.GPR 4#5) s ≠ 0#64 ∧ read_mem_bytes 8 (r (.GPR 3#5) s) s = b) :
    let t := block base (kind.ops (sumOverflow a b)) s
    r (.GPR 11#5) t = a + b ∧
      r (.GPR 12#5) t = (if 2^64 ≤ a.toNat + b.toNat then 1#64 else 0#64) ∧
      (kind ≠ .smallLarge → r (.GPR 13#5) t = if kind = .largeSmall then 1#64 else 0#64) ∧
      (kind ≠ .smallLarge → r (.GPR 14#5) t = r (.GPR 8#5) s) ∧
      (kind ≠ .smallLarge → r (.GPR 15#5) t = 1#64) ∧
      read_pc t = base + (if kind = .smallLarge then 1868#64 else 1692#64) := by
  cases kind <;> simp at leftKind left right
  all_goals
    by_cases overflow : 2^64 ≤ a.toNat + b.toNat <;>
      simp [FirstKind.ops, sumOverflow, overflow, block, Op.effect, put, next,
        state_simp_rules, leftKind, left, right]

/-- There is exactly one payload write in each first-word path. -/
theorem first_word_memory (s : ArmState) (base a b : BitVec 64) (kind : FirstKind)
    (left : if kind = .smallLarge then r (.GPR 2#5) s = a else
      r (.GPR 2#5) s ≠ 0#64 ∧ read_mem_bytes 8 (r (.GPR 1#5) s) s = a)
    (right : if kind = .largeSmall then r (.GPR 4#5) s = b else
      r (.GPR 4#5) s ≠ 0#64 ∧ read_mem_bytes 8 (r (.GPR 3#5) s) s = b) :
    (block base (kind.ops (sumOverflow a b)) s).mem =
      (write_mem_bytes 8 (r (.GPR 9#5) s) (a + b) s).mem := by
  cases kind <;> simp at left right
  all_goals
    by_cases overflow : 2^64 ≤ a.toNat + b.toNat <;>
      simp [FirstKind.ops, sumOverflow, overflow, block, Op.effect, put, next,
        state_simp_rules, left, right, NatCompare.spill_mem_w]

/-- Only X11 through X15 are modified, independently of the branch choice. -/
theorem first_word_registers (s : ArmState) (base : BitVec 64)
    (kind : FirstKind) (overflow : Bool) :
    ∀ reg : BitVec 5, reg ∉ [11#5, 12#5, 13#5, 14#5, 15#5] →
      r (.GPR reg) (block base (kind.ops overflow) s) = r (.GPR reg) s := by
  intro reg outside
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  cases kind <;> cases overflow <;>
    simp (disch := simp_all) [FirstKind.ops, block, Op.effect, put, next, state_simp_rules]

theorem first_word_vectors (s : ArmState) (base : BitVec 64)
    (kind : FirstKind) (overflow : Bool) :
    ∀ reg : BitVec 5, r (.SFP reg) (block base (kind.ops overflow) s) = r (.SFP reg) s := by
  intro reg
  cases kind <;> cases overflow <;>
    simp [FirstKind.ops, block, Op.effect, put, next, state_simp_rules]

end SszArm.NatAdd

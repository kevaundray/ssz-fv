import SszArm.NatMulWordExec
import SszArm.NatMulWordStep
import SszArm.NatMulStateFold

namespace SszArm.NatMulWord

def roundTailOps (s : ArmState) : List Op :=
  if r (.FLAG .C) s = 1#1 then [.p784, .p788, .p800, .p804, .p808]
  else [.p784, .p788, .p792, .p796, .p804, .p808]

def roundTail (s : ArmState) (base : BitVec 64) : ArmState :=
  block base (roundTailOps s) s

theorem round_tail_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 784#64) :
    run (roundTailOps s).length s = roundTail s base := by
  apply block_run base (roundTailOps s) s code error aligned
  have hpc : r .PC s = base + 784#64 := pc
  by_cases carry : r (.FLAG .C) s = 1#1 <;>
    simp [roundTailOps, carry, Follows, Op.row, Op.effect, put, next,
      Udivti3.compare, Udivti3.next, state_simp_rules, hpc, BitVec.add_assoc]

theorem round_tail_pc (s : ArmState) (base : BitVec 64) :
    read_pc (roundTail s base) =
      if r (.GPR 9#5) s = r (.GPR 16#5) s then base + 1464#64 else base + 812#64 := by
  by_cases carry : r (.FLAG .C) s = 1#1 <;>
    simp [roundTail, roundTailOps, carry, block, Op.effect, put, next,
      Udivti3.compare, Udivti3.next, state_simp_rules, Udivti3.cmp_zero]

theorem round_tail_index (s : ArmState) (base : BitVec 64) :
    r (.GPR 13#5) (roundTail s base) = r (.GPR 16#5) s := by
  by_cases carry : r (.FLAG .C) s = 1#1 <;>
    simp [roundTail, roundTailOps, carry, block, Op.effect, put, next,
      Udivti3.compare, Udivti3.next, state_simp_rules]

theorem round_tail_carry (s : ArmState) (base : BitVec 64) :
    r (.GPR 14#5) (roundTail s base) = r (.GPR 17#5) s +
      (if r (.FLAG .C) s = 1#1 then 1#64 else 0#64) := by
  by_cases carry : r (.FLAG .C) s = 1#1 <;>
    simp [roundTail, roundTailOps, carry, block, Op.effect, put, next,
      Udivti3.compare, Udivti3.next, state_simp_rules]

theorem round_tail_registers (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (index : reg ≠ 13#5) (carryReg : reg ≠ 14#5) :
    r (.GPR reg) (roundTail s base) = r (.GPR reg) s := by
  refine NatMulStateFold.preserves (fun t (op : Op) => op.effect base t)
    (fun t => r (.GPR reg) t) (roundTailOps s) s ?_
  intro op member t
  by_cases carry : r (.FLAG .C) s = 1#1
  · simp only [roundTailOps, carry, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      simp_all (config := {decide := true}) [Op.effect, put, next,
        Udivti3.compare, Udivti3.next, state_simp_rules]
  · simp only [roundTailOps, carry, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all (config := {decide := true}) [Op.effect, put, next,
        Udivti3.compare, Udivti3.next, state_simp_rules]

theorem round_tail_memory (s : ArmState) (base : BitVec 64) :
    (roundTail s base).mem = s.mem := by
  by_cases carry : r (.FLAG .C) s = 1#1 <;>
    simp [roundTail, roundTailOps, carry, block, Op.effect, put, next,
      Udivti3.compare, Udivti3.next, state_simp_rules]

end SszArm.NatMulWord

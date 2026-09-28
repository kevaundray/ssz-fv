import SszArm.EmitBitsEntry

namespace SszArm.Emit.Bits

open Dispatch (next compare64 branch)
open Activation (put)

inductive Guard where
  | listCapacity | vectorCapacity | listBacking | vectorBacking | vectorTag
  deriving DecidableEq

def Guard.start : Guard → Nat
  | .listCapacity => 608 | .vectorCapacity => 1216
  | .listBacking => 620 | .vectorBacking => 1228 | .vectorTag => 1180

def Guard.ops : Guard → List Op
  | .listCapacity => [.p608, .p612] | .vectorCapacity => [.p1216, .p1220]
  | .listBacking => [.p620, .p624] | .vectorBacking => [.p1228, .p1232]
  | .vectorTag => [.p1180, .p1184]

def Guard.left : Guard → BitVec 5
  | .listCapacity | .vectorCapacity => 21#5
  | .listBacking | .vectorBacking => 24#5
  | .vectorTag => 8#5

def Guard.right (guard : Guard) (s : ArmState) : BitVec 64 :=
  match guard with
  | .vectorTag => 4#64
  | _ => r (.GPR 23#5) s

def Guard.good (guard : Guard) (s : ArmState) : Prop :=
  match guard with
  | .vectorTag => r (.GPR 8#5) s = 4#64
  | _ => (guard.right s).toNat ≤ (r (.GPR guard.left) s).toNat

@[irreducible] def guarded (guard : Guard) (s : ArmState) : ArmState :=
  block guard.ops s

theorem guard_follows (guard : Guard) (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 guard.start) : Follows base guard.ops s := by
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  cases guard <;>
    simp (config := {decide := true, instances := true})
      [Follows, Guard.ops, Guard.start, Op.row, Op.effect, compare64, Dispatch.next,
       state_simp_rules, aligned, CheckSPAlignment, stack, pc, BitVec.add_assoc]

theorem guard_run (guard : Guard) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 guard.start) :
    run 2 s = guarded guard s := by
  rw [guarded, show 2 = guard.ops.length by cases guard <;> rfl]
  exact runs guard.ops s base code error (guard_follows guard s base aligned pc)

theorem guarded_pc (guard : Guard) (s : ArmState) (good : guard.good s) :
    read_pc (guarded guard s) = read_pc s + 8#64 := by
  cases guard <;>
    simp only [Guard.good, Guard.left, Guard.right, ← BitVec.le_def] at good
  all_goals
    simp (config := {decide := true})
      [guarded, block, Guard.ops, Op.effect, compare64, Dispatch.next, branch,
       state_simp_rules, Udivti3.cmp_carry, Udivti3.cmp_zero, good, BitVec.add_assoc]

@[simp] theorem guarded_program (guard : Guard) (s : ArmState) :
    (guarded guard s).program = s.program := by
  cases guard <;> simp [guarded, block, Guard.ops]

@[simp] theorem guarded_error (guard : Guard) (s : ArmState) :
    read_err (guarded guard s) = read_err s := by
  cases guard <;> simp [guarded, block, Guard.ops]

@[simp] theorem guarded_memory (guard : Guard) (s : ArmState) :
    (guarded guard s).mem = s.mem := by
  cases guard <;> simp [guarded, block, Guard.ops, Op.effect, compare64,
    Dispatch.next, branch, state_simp_rules]

@[simp] theorem guarded_register (guard : Guard) (s : ArmState) (reg : BitVec 5) :
    r (.GPR reg) (guarded guard s) = r (.GPR reg) s := by
  cases guard <;> simp [guarded, block, Guard.ops, Op.effect, compare64,
    Dispatch.next, branch, state_simp_rules]

@[simp] theorem guarded_vector (guard : Guard) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (guarded guard s) = r (.SFP reg) s := by
  cases guard <;> simp [guarded, block, Guard.ops, Op.effect, compare64,
    Dispatch.next, branch, state_simp_rules]

end SszArm.Emit.Bits

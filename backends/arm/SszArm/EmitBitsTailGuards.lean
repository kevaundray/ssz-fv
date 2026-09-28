import SszArm.EmitBitsWork
import SszArm.EmitBitsTailOps

namespace SszArm.Emit.Bits

inductive TailGuard where
  | listBacking | vectorBacking | listCapacity | vectorCapacity | listLast | vectorLast
  deriving DecidableEq

def TailGuard.start : TailGuard → Nat
  | .listBacking => 656 | .vectorBacking => 1256
  | .listCapacity => 1488 | .vectorCapacity => 1264
  | .listLast => 696 | .vectorLast => 1304

def TailGuard.ops : TailGuard → List Tail.Op
  | .listBacking => [.p656, .p660] | .vectorBacking => [.p1256, .p1260]
  | .listCapacity => [.p1488, .p1492] | .vectorCapacity => [.p1264, .p1268]
  | .listLast => [.p696, .p700] | .vectorLast => [.p1304, .p1308]

def TailGuard.good (guard : TailGuard) (s : ArmState) : Prop :=
  match guard with
  | .listBacking | .vectorBacking => (r (.GPR 23#5) s).toNat < (r (.GPR 24#5) s).toNat
  | .listCapacity | .vectorCapacity => (r (.GPR 23#5) s).toNat < (r (.GPR 21#5) s).toNat
  | .listLast | .vectorLast => r (.GPR 9#5) s = r (.GPR 24#5) s

@[irreducible] def tailGuarded (guard : TailGuard) (s : ArmState) : ArmState := Tail.block guard.ops s

theorem tail_guard_follows (guard : TailGuard) (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + BitVec.ofNat 64 guard.start) :
    Tail.Follows base guard.ops s := by
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  cases guard <;> simp [TailGuard.ops, TailGuard.start, Tail.Follows, Tail.Op.row, Tail.Op.effect,
    Dispatch.compare64, Dispatch.next, state_simp_rules, aligned, CheckSPAlignment, stack, pc, BitVec.add_assoc]

theorem tail_guard_run (guard : TailGuard) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 guard.start) :
    run 2 s = tailGuarded guard s := by
  rw [tailGuarded, show 2 = guard.ops.length by cases guard <;> rfl]
  exact Tail.runs _ s base code error (tail_guard_follows guard s base aligned pc)

theorem tailGuarded_pc (guard : TailGuard) (s : ArmState) (good : guard.good s) :
    read_pc (tailGuarded guard s) = read_pc s + 8#64 := by
  cases guard <;> simp only [TailGuard.good] at good
  all_goals
    simp (config := {decide := true}) [tailGuarded, Tail.block, TailGuard.ops, Tail.Op.effect,
      Tail.lowerOrSame, Dispatch.branch, Dispatch.compare64, Dispatch.next, state_simp_rules,
      Udivti3.cmp_zero, good, BitVec.add_assoc]
  all_goals
    have flags := (Udivti3.cmp_high _ _).2 good
    have different := (Udivti3.cmp_nonzero _ _).1 flags.2
    simp (config := {decide := true}) [flags.1, different]

theorem vector_aligned_pc (s : ArmState)
    (same : r (.GPR 24#5) s = r (.GPR 23#5) s) :
    read_pc (tailGuarded .vectorBacking s) = read_pc s + 324#64 := by
  simp (config := {decide := true}) [tailGuarded, Tail.block, TailGuard.ops, Tail.Op.effect,
    Tail.lowerOrSame, Dispatch.branch, Dispatch.compare64, Dispatch.next, state_simp_rules,
    Udivti3.cmp_high, same, BitVec.add_assoc]

@[simp] theorem tailGuarded_program (guard : TailGuard) (s : ArmState) :
    (tailGuarded guard s).program = s.program := by cases guard <;> simp [tailGuarded, Tail.block, TailGuard.ops]

@[simp] theorem tailGuarded_error (guard : TailGuard) (s : ArmState) :
    read_err (tailGuarded guard s) = read_err s := by cases guard <;> simp [tailGuarded, Tail.block, TailGuard.ops]

@[simp] theorem tailGuarded_memory (guard : TailGuard) (s : ArmState) :
    (tailGuarded guard s).mem = s.mem := by
  cases guard <;> simp [tailGuarded, Tail.block, TailGuard.ops, Tail.Op.effect,
    Dispatch.branch, Dispatch.compare64, Dispatch.next, state_simp_rules]

@[simp] theorem tailGuarded_register (guard : TailGuard) (s : ArmState) (reg : BitVec 5) :
    r (.GPR reg) (tailGuarded guard s) = r (.GPR reg) s := by
  cases guard <;> simp [tailGuarded, Tail.block, TailGuard.ops, Tail.Op.effect,
    Dispatch.branch, Dispatch.compare64, Dispatch.next, state_simp_rules]

@[simp] theorem tailGuarded_vector (guard : TailGuard) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (tailGuarded guard s) = r (.SFP reg) s := by
  cases guard <;> simp [tailGuarded, Tail.block, TailGuard.ops, Tail.Op.effect,
    Dispatch.branch, Dispatch.compare64, Dispatch.next, state_simp_rules]

end SszArm.Emit.Bits

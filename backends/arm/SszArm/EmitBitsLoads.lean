import SszArm.EmitBitsGuards

namespace SszArm.Emit.Bits

open Activation (put)

def Path.countStart : Path → Nat
  | .list => 580 | .vector => 1188

def Path.countOp : Path → Op
  | .list => .p580 | .vector => .p1188

def Path.backingStart : Path → Nat
  | .list => 616 | .vector => 1224

def Path.backingOp : Path → Op
  | .list => .p616 | .vector => .p1224

def Path.setupStart : Path → Nat
  | .list => 628 | .vector => 1236

def Path.setupOps : Path → List Op
  | .list => [.p628, .p632, .p636, .p640, .p644]
  | .vector => [.p1236, .p1240, .p1244, .p1248]

@[irreducible] def counted (path : Path) (s : ArmState) : ArmState := countPair path.low s

@[irreducible] def backingLoaded (s : ArmState) : ArmState :=
  put 24 (read_mem_bytes 8 (r (.GPR 22#5) s + 24#64) s) s

@[irreducible] def ready (path : Path) (s : ArmState) : ArmState := block path.setupOps s

theorem count_run (path : Path) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 path.countStart) :
    run 1 s = counted path s := by
  have position : read_pc s = base + BitVec.ofNat 64 path.countOp.row.1 := by
    cases path <;> exact pc
  change stepi s = _
  rw [step path.countOp s base code error aligned position]
  unfold counted
  cases path <;> rfl

theorem backing_run (path : Path) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 path.backingStart) :
    run 1 s = backingLoaded s := by
  have position : read_pc s = base + BitVec.ofNat 64 path.backingOp.row.1 := by
    cases path <;> exact pc
  change stepi s = _
  rw [step path.backingOp s base code error aligned position]
  unfold backingLoaded
  cases path <;> rfl

theorem setup_follows (path : Path) (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 path.setupStart) :
    Follows base path.setupOps s := by
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  cases path <;>
    simp (config := {decide := true, instances := true})
      [Path.setupOps, Path.setupStart, Follows, Op.row, Op.effect, Activation.put,
       Activation.next, state_simp_rules, aligned, CheckSPAlignment, stack, pc, BitVec.add_assoc]

theorem setup_run (path : Path) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 path.setupStart) :
    run path.setupOps.length s = ready path s := by
  rw [ready]
  exact runs path.setupOps s base code error (setup_follows path s base aligned pc)

@[simp] theorem counted_program (path : Path) (s : ArmState) :
    (counted path s).program = s.program := by
  simp [counted, countPair, Activation.put, Activation.next, state_simp_rules]

@[simp] theorem counted_error (path : Path) (s : ArmState) :
    read_err (counted path s) = read_err s := by
  simp [counted, countPair, Activation.put, Activation.next, state_simp_rules]

@[simp] theorem counted_memory (path : Path) (s : ArmState) :
    (counted path s).mem = s.mem := by
  simp [counted, countPair, Activation.put, Activation.next, state_simp_rules]

@[simp] theorem counted_pc (path : Path) (s : ArmState) :
    read_pc (counted path s) = read_pc s + 4#64 := by
  simp [counted, countPair, Activation.put, Activation.next, state_simp_rules]

@[simp] theorem counted_low (path : Path) (s : ArmState) :
    r (.GPR path.low) (counted path s) = read_mem_bytes 8 (r (.GPR 22#5) s + 32#64) s := by
  cases path <;> simp [counted, countPair, Path.low, Activation.put, Activation.next, state_simp_rules]

@[simp] theorem counted_high (path : Path) (s : ArmState) :
    r (.GPR 8#5) (counted path s) = read_mem_bytes 8 (r (.GPR 22#5) s + 40#64) s := by
  simp [counted, countPair, Activation.put, Activation.next, state_simp_rules]

@[simp] theorem counted_register (path : Path) (s : ArmState) (reg : BitVec 5)
    (notLow : reg ≠ path.low) (notHigh : reg ≠ 8#5) :
    r (.GPR reg) (counted path s) = r (.GPR reg) s := by
  simp [counted, countPair, Activation.put, Activation.next, state_simp_rules, notLow, notHigh]

@[simp] theorem backing_program (s : ArmState) : (backingLoaded s).program = s.program := by
  simp [backingLoaded, Activation.put, Activation.next, state_simp_rules]

@[simp] theorem backing_error (s : ArmState) : read_err (backingLoaded s) = read_err s := by
  simp [backingLoaded, Activation.put, Activation.next, state_simp_rules]

@[simp] theorem backing_memory (s : ArmState) : (backingLoaded s).mem = s.mem := by
  simp [backingLoaded, Activation.put, Activation.next, state_simp_rules]

@[simp] theorem backing_pc (s : ArmState) : read_pc (backingLoaded s) = read_pc s + 4#64 := by
  simp [backingLoaded, Activation.put, Activation.next, state_simp_rules]

@[simp] theorem backing_length (s : ArmState) :
    r (.GPR 24#5) (backingLoaded s) = read_mem_bytes 8 (r (.GPR 22#5) s + 24#64) s := by
  simp [backingLoaded, Activation.put, Activation.next, state_simp_rules]

@[simp] theorem backing_register (s : ArmState) (reg : BitVec 5) (other : reg ≠ 24#5) :
    r (.GPR reg) (backingLoaded s) = r (.GPR reg) s := by
  simp [backingLoaded, Activation.put, Activation.next, state_simp_rules, other]

@[simp] theorem ready_program (path : Path) (s : ArmState) : (ready path s).program = s.program := by
  cases path <;> simp [ready, block, Path.setupOps]

@[simp] theorem ready_error (path : Path) (s : ArmState) : read_err (ready path s) = read_err s := by
  cases path <;> simp [ready, block, Path.setupOps]

@[simp] theorem ready_memory (path : Path) (s : ArmState) : (ready path s).mem = s.mem := by
  cases path <;> simp [ready, block, Path.setupOps, Op.effect, Activation.put, Activation.next,
    state_simp_rules]

@[simp] theorem ready_arguments (path : Path) (s : ArmState) :
    r (.GPR 0#5) (ready path s) = r (.GPR 20#5) s ∧
    r (.GPR 1#5) (ready path s) = read_mem_bytes 8 (r (.GPR 22#5) s + 16#64) s ∧
    r (.GPR 2#5) (ready path s) = r (.GPR 23#5) s := by
  cases path <;> simp [ready, block, Path.setupOps, Op.effect, Activation.put, Activation.next,
    state_simp_rules]

end SszArm.Emit.Bits

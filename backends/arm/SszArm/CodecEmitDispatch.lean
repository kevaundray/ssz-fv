import SszArm.CodecLinkedEmit
import SszArm.EmitDispatchOps

namespace SszArm.Codec.Emit.Dispatch

open SszArm.Emit.Dispatch (next branch compare64 compare32 greater)

/-- The compound routes after the shared primitive tag comparisons. -/
inductive Op where
  | p48 | p52 | p56 | p544 | p548
  | p740 | p744 | p748 | p752 | p756 | p760 | p764
  | p868 | p872 | p876 | p880 | p884 | p888 | p892
  | p1368 | p1372 | p1376 | p1380 | p1384 | p1388
  | p1392 | p1396 | p1400 | p1536
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p48 => (48, 0xb4000948#32)
  | .p52 => (52, 0xf100051f#32)
  | .p56 => (56, 0x54000f41#32)
  | .p544 => (544, 0x71000d3f#32)
  | .p548 => (548, 0x5400060c#32)
  | .p740 => (740, 0xaa0303e4#32)
  | .p744 => (744, 0x7100113f#32)
  | .p748 => (748, 0x540003c0#32)
  | .p752 => (752, 0x7100153f#32)
  | .p756 => (756, 0x54fff341#32)
  | .p760 => (760, 0xf100311f#32)
  | .p764 => (764, 0x54fff301#32)
  | .p868 => (868, 0xf100251f#32)
  | .p872 => (872, 0x54000f8c#32)
  | .p876 => (876, 0xd1001d09#32)
  | .p880 => (880, 0xf100093f#32)
  | .p884 => (884, 0x54000fe2#32)
  | .p888 => (888, 0x52800308#32)
  | .p892 => (892, 0x14000080#32)
  | .p1368 => (1368, 0xf100291f#32)
  | .p1372 => (1372, 0x54000520#32)
  | .p1376 => (1376, 0xf1002d1f#32)
  | .p1380 => (1380, 0x54ffdfc1#32)
  | .p1384 => (1384, 0x52800308#32)
  | .p1388 => (1388, 0x14000026#32)
  | .p1392 => (1392, 0xf100251f#32)
  | .p1396 => (1396, 0x54ffdf41#32)
  | .p1400 => (1400, 0x52800108#32)
  | .p1536 => (1536, 0x52800108#32)

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

def Op.effect : Op → ArmState → ArmState
  | .p48, s => branch (r (.GPR 8#5) s = 0#64) 296#64 s
  | .p52, s => compare64 (r (.GPR 8#5) s) 1#64 s
  | .p56, s => branch (r (.FLAG .Z) s ≠ 1#1) 488#64 s
  | .p544, s => compare32 ((r (.GPR 9#5) s).setWidth 32) 3#32 s
  | .p548, s => branch (greater s) 192#64 s
  | .p740, s => put 4 (r (.GPR 3#5) s) s
  | .p744, s => compare32 ((r (.GPR 9#5) s).setWidth 32) 4#32 s
  | .p748, s => branch (r (.FLAG .Z) s = 1#1) 120#64 s
  | .p752, s => compare32 ((r (.GPR 9#5) s).setWidth 32) 5#32 s
  | .p756, s => branch (r (.FLAG .Z) s ≠ 1#1) (-408#64) s
  | .p760, s => compare64 (r (.GPR 8#5) s) 12#64 s
  | .p764, s => branch (r (.FLAG .Z) s ≠ 1#1) (-416#64) s
  | .p868, s => compare64 (r (.GPR 8#5) s) 9#64 s
  | .p872, s => branch (greater s) 496#64 s
  | .p876, s => put 9 (r (.GPR 8#5) s - 7#64) s
  | .p880, s => compare64 (r (.GPR 9#5) s) 2#64 s
  | .p884, s => branch (r (.FLAG .C) s = 1#1) 508#64 s
  | .p888, s => put 8 24#64 s
  | .p892, s => w .PC (read_pc s + 512#64) s
  | .p1368, s => compare64 (r (.GPR 8#5) s) 10#64 s
  | .p1372, s => branch (r (.FLAG .Z) s = 1#1) 164#64 s
  | .p1376, s => compare64 (r (.GPR 8#5) s) 11#64 s
  | .p1380, s => branch (r (.FLAG .Z) s ≠ 1#1) (-1032#64) s
  | .p1384, s => put 8 24#64 s
  | .p1388, s => w .PC (read_pc s + 152#64) s
  | .p1392, s => compare64 (r (.GPR 8#5) s) 9#64 s
  | .p1396, s => branch (r (.FLAG .Z) s ≠ 1#1) (-1048#64) s
  | .p1400, s => put 8 8#64 s
  | .p1536, s => put 8 8#64 s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.Emit.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect s := by
  have fetched := code op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, put, next, branch, compare64, compare32, greater,
       exec_inst, state_simp_rules, bitvec_rules, minimal_theory, apply_ite,
       BitVec.sub_eq_add_neg]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (by_cases n : r (.FLAG .N) s = r (.FLAG .V) s <;>
        by_cases z : r (.FLAG .Z) s = 0#1 <;> simp_all)
    | (split <;> simp_all)

@[simp] theorem Op.program (op : Op) (s : ArmState) :
    (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, put, next, branch, compare64, compare32, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) :
    read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, put, next, branch, compare64, compare32, state_simp_rules]

@[simp] theorem Op.memory (op : Op) (s : ArmState) :
    (op.effect s).mem = s.mem := by
  cases op <;> simp [Op.effect, put, next, branch, compare64, compare32, state_simp_rules]

@[simp] theorem Op.register (op : Op) (s : ArmState) (reg : BitVec 5)
    (untouched : reg ∉ [4#5, 8#5, 9#5]) :
    r (.GPR reg) (op.effect s) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.mem_singleton, not_or] at untouched
  cases op <;> simp [Op.effect, put, next, branch, compare64, compare32,
    state_simp_rules, untouched.1, untouched.2.1, untouched.2.2]

@[simp] theorem Op.vector (op : Op) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (op.effect s) = r (.SFP reg) s := by
  cases op <;> simp [Op.effect, put, next, branch, compare64, compare32, state_simp_rules]

def block (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      Follows base ops (op.effect s)

theorem runs (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.Emit.CodeAt s base) (error : read_err s = .None)
    (follows : Follows base ops s) : run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = block ops (op.effect s)
    rw [run, step op s base code error follows.1]
    exact ih _ (Linked.WordsAt.preserve code (op.program s))
      ((op.error s).trans error) follows.2

@[simp] theorem block_program (ops : List Op) (s : ArmState) :
    (block ops s).program = s.program := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.program s)

@[simp] theorem block_error (ops : List Op) (s : ArmState) :
    read_err (block ops s) = read_err s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.error s)

@[simp] theorem block_memory (ops : List Op) (s : ArmState) :
    (block ops s).mem = s.mem := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.memory s)

@[simp] theorem block_register (ops : List Op) (s : ArmState) (reg : BitVec 5)
    (untouched : reg ∉ [4#5, 8#5, 9#5]) :
    r (.GPR reg) (block ops s) = r (.GPR reg) s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.register s reg untouched)

@[simp] theorem block_vector (ops : List Op) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (block ops s) = r (.SFP reg) s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.vector s reg)

/-- These are physical dispatch cases, not a second codec interpretation. -/
inductive Kind where
  | vector | list | progressiveList | container | progressiveContainer | union
  deriving DecidableEq

def Kind.tag : Kind → BitVec 64
  | .vector => 7 | .list => 8 | .progressiveList => 9
  | .container => 10 | .progressiveContainer => 11 | .union => 12

def Kind.valueTag : Kind → BitVec 64
  | .union => 5 | _ => 4

def Kind.ops (kind : Kind) : List Op :=
  [.p48, .p52, .p56, .p544, .p548, .p740, .p744, .p748] ++
  match kind with
  | .vector | .list => [.p868, .p872, .p876, .p880, .p884, .p888, .p892]
  | .progressiveList => [.p868, .p872, .p876, .p880, .p884, .p1392, .p1396, .p1400]
  | .container => [.p868, .p872, .p1368, .p1372, .p1536]
  | .progressiveContainer => [.p868, .p872, .p1368, .p1372, .p1376, .p1380, .p1384, .p1388]
  | .union => [.p752, .p756, .p760, .p764]

def Kind.destination : Kind → Nat
  | .vector | .list | .progressiveList => 1404
  | .container | .progressiveContainer => 1540
  | .union => 768

def Kind.payload : Kind → BitVec 64
  | .vector | .list | .progressiveContainer => 24
  | .progressiveList | .container => 8
  | .union => 12

theorem follows (kind : Kind) (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 48#64)
    (tag : r (.GPR 8#5) s = kind.tag)
    (valueTag : r (.GPR 9#5) s = kind.valueTag) :
    Follows base kind.ops s := by
  change r .PC s = _ at pc
  cases kind <;>
    simp (config := {decide := true, instances := true})
      [Kind.ops, Kind.tag, Kind.valueTag, Follows, Op.row, Op.effect,
       put, next, branch, compare64, compare32, greater,
       state_simp_rules, bitvec_rules, minimal_theory, pc, tag, valueTag,
       BitVec.add_assoc]

theorem destination (kind : Kind) (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 48#64)
    (tag : r (.GPR 8#5) s = kind.tag)
    (valueTag : r (.GPR 9#5) s = kind.valueTag) :
    read_pc (block kind.ops s) = base + BitVec.ofNat 64 kind.destination ∧
      r (.GPR 8#5) (block kind.ops s) = kind.payload ∧
      r (.GPR 4#5) (block kind.ops s) = r (.GPR 3#5) s := by
  change r .PC s = _ at pc
  cases kind <;>
    simp (config := {decide := true, instances := true})
      [Kind.ops, Kind.tag, Kind.valueTag, Kind.destination, Kind.payload,
       block, Op.effect, put, next, branch, compare64, compare32, greater,
       state_simp_rules, bitvec_rules, minimal_theory, pc, tag, valueTag,
       BitVec.add_assoc]

theorem route (kind : Kind) (s : ArmState) (base : BitVec 64)
    (code : Linked.Emit.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 48#64)
    (tag : r (.GPR 8#5) s = kind.tag)
    (valueTag : r (.GPR 9#5) s = kind.valueTag) :
    run kind.ops.length s = block kind.ops s ∧
      read_pc (block kind.ops s) = base + BitVec.ofNat 64 kind.destination ∧
      r (.GPR 8#5) (block kind.ops s) = kind.payload ∧
      r (.GPR 4#5) (block kind.ops s) = r (.GPR 3#5) s :=
  ⟨runs _ s base code error (follows kind s base pc tag valueTag),
    destination kind s base pc tag valueTag⟩

end SszArm.Codec.Emit.Dispatch

import SszArm.IndicesLinkedElementType
import SszArm.EmitDispatchOps

set_option autoImplicit false

namespace SszArm.Indices.ElementType.Dispatch

open SszArm.Emit.Dispatch (next branch compare64 greater)

inductive Op where
  | p12 | p16 | p20 | p24 | p28 | p32 | p36 | p40 | p44 | p48 | p52 | p56 | p144 | p148 | p152 | p156 | p252 | p256 | p260 | p264 | p268 | p272 | p276 | p280 | p372 | p376 | p380 | p384 | p388 | p612
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p12 => (12, 0xf100191f#32)
  | .p16 => (16, 0xb40000e9#32)
  | .p20 => (20, 0x540000ed#32)
  | .p24 => (24, 0xd1001d09#32)
  | .p28 => (28, 0xf100093f#32)
  | .p32 => (32, 0x54000782#32)
  | .p36 => (36, 0x52800308#32)
  | .p40 => (40, 0x1400003d#32)
  | .p44 => (44, 0x5400068c#32)
  | .p48 => (48, 0xd1001109#32)
  | .p52 => (52, 0xf1000d3f#32)
  | .p56 => (56, 0x540002c2#32)
  | .p144 => (144, 0xd1000908#32)
  | .p148 => (148, 0xf100091f#32)
  | .p152 => (152, 0x54000802#32)
  | .p156 => (156, 0x52800028#32)
  | .p252 => (252, 0xf100251f#32)
  | .p256 => (256, 0x540003ac#32)
  | .p260 => (260, 0xd1001d09#32)
  | .p264 => (264, 0xf100093f#32)
  | .p268 => (268, 0x54fff8c3#32)
  | .p272 => (272, 0xf100251f#32)
  | .p276 => (276, 0x54000421#32)
  | .p280 => (280, 0x52800108#32)
  | .p372 => (372, 0xf100291f#32)
  | .p376 => (376, 0x54000760#32)
  | .p380 => (380, 0xf1002d1f#32)
  | .p384 => (384, 0x540000c1#32)
  | .p388 => (388, 0x5280030a#32)
  | .p612 => (612, 0x5280010a#32)

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

def Op.effect : Op → ArmState → ArmState
  | .p12, s => compare64 (r (.GPR 8#5) s) 6#64 s
  | .p16, s => branch (r (.GPR 9#5) s = 0#64) 28#64 s
  | .p20, s => branch (¬ greater s) 28#64 s
  | .p24, s => put 9 (r (.GPR 8#5) s - 7#64) s
  | .p28, s => compare64 (r (.GPR 9#5) s) 2#64 s
  | .p32, s => branch (r (.FLAG .C) s = 1#1) 240#64 s
  | .p36, s => put 8 24#64 s
  | .p40, s => w .PC (read_pc s + 244#64) s
  | .p44, s => branch (greater s) 208#64 s
  | .p48, s => put 9 (r (.GPR 8#5) s - 4#64) s
  | .p52, s => compare64 (r (.GPR 9#5) s) 3#64 s
  | .p56, s => branch (r (.FLAG .C) s = 1#1) 88#64 s
  | .p144, s => put 8 (r (.GPR 8#5) s - 2#64) s
  | .p148, s => compare64 (r (.GPR 8#5) s) 2#64 s
  | .p152, s => branch (r (.FLAG .C) s = 1#1) 256#64 s
  | .p156, s => put 8 1#64 s
  | .p252, s => compare64 (r (.GPR 8#5) s) 9#64 s
  | .p256, s => branch (greater s) 116#64 s
  | .p260, s => put 9 (r (.GPR 8#5) s - 7#64) s
  | .p264, s => compare64 (r (.GPR 9#5) s) 2#64 s
  | .p268, s => branch (r (.FLAG .C) s ≠ 1#1) (-232#64) s
  | .p272, s => compare64 (r (.GPR 8#5) s) 9#64 s
  | .p276, s => branch (r (.FLAG .Z) s ≠ 1#1) 132#64 s
  | .p280, s => put 8 8#64 s
  | .p372, s => compare64 (r (.GPR 8#5) s) 10#64 s
  | .p376, s => branch (r (.FLAG .Z) s = 1#1) 236#64 s
  | .p380, s => compare64 (r (.GPR 8#5) s) 11#64 s
  | .p384, s => branch (r (.FLAG .Z) s ≠ 1#1) 24#64 s
  | .p388, s => put 10 24#64 s
  | .p612, s => put 10 8#64 s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.ElementType.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect s := by
  have fetched := code op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, put, next, branch, compare64, greater,
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
  cases op <;> simp [Op.effect, put, next, branch, compare64, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) :
    read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, put, next, branch, compare64, state_simp_rules]

@[simp] theorem Op.memory (op : Op) (s : ArmState) :
    (op.effect s).mem = s.mem := by
  cases op <;> simp [Op.effect, put, next, branch, compare64, state_simp_rules]

@[simp] theorem Op.sp (op : Op) (s : ArmState) :
    r (.GPR 31#5) (op.effect s) = r (.GPR 31#5) s := by
  cases op <;> simp [Op.effect, put, next, branch, compare64, state_simp_rules]

def block (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      Follows base ops (op.effect s)

theorem block_run (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.ElementType.CodeAt s base) (error : read_err s = .None)
    (follows : Follows base ops s) : run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops induction =>
      change run (ops.length + 1) s = block ops (op.effect s)
      rw [run, step op s base code error follows.1]
      exact induction _ (Codec.Linked.WordsAt.preserve code (op.program s))
        ((op.error s).trans error) follows.2

end SszArm.Indices.ElementType.Dispatch

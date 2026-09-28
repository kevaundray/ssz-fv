import SszArm.EmitContract

namespace SszArm.Emit.Dispatch

inductive Op where
  | p48 | p52 | p56 | p544 | p548 | p552 | p556 | p560 | p564
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p48 => (48, 0xb4000948#32)
  | .p52 => (52, 0xf100051f#32)
  | .p56 => (56, 0x54000f41#32)
  | .p544 => (544, 0x71000d3f#32)
  | .p548 => (548, 0x5400060c#32)
  | .p552 => (552, 0x7100093f#32)
  | .p556 => (556, 0x54000840#32)
  | .p560 => (560, 0x71000d3f#32)
  | .p564 => (564, 0x54fff941#32)

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def branch (condition : Prop) [Decidable condition] (delta : BitVec 64)
    (s : ArmState) : ArmState :=
  w .PC (read_pc s + if condition then delta else 4#64) s

def compare64 (left right : BitVec 64) (s : ArmState) : ArmState :=
  write_pstate (AddWithCarry left (~~~right) 1#1).2 (next s)

def compare32 (left right : BitVec 32) (s : ArmState) : ArmState :=
  write_pstate (AddWithCarry left (~~~right) 1#1).2 (next s)

def greater (s : ArmState) : Prop :=
  r (.FLAG .N) s = r (.FLAG .V) s ∧ r (.FLAG .Z) s = 0#1

instance (s : ArmState) : Decidable (greater s) := inferInstanceAs (Decidable (_ ∧ _))

def Op.effect : Op → ArmState → ArmState
  | .p48, s => branch (r (.GPR 8#5) s = 0#64) 296#64 s
  | .p52, s => compare64 (r (.GPR 8#5) s) 1#64 s
  | .p56, s => branch (r (.FLAG .Z) s ≠ 1#1) 488#64 s
  | .p544, s => compare32 ((r (.GPR 9#5) s).setWidth 32) 3#32 s
  | .p548, s => branch (greater s) 192#64 s
  | .p552, s => compare32 ((r (.GPR 9#5) s).setWidth 32) 2#32 s
  | .p556, s => branch (r (.FLAG .Z) s = 1#1) 264#64 s
  | .p560, s => compare32 ((r (.GPR 9#5) s).setWidth 32) 3#32 s
  | .p564, s => branch (r (.FLAG .Z) s ≠ 1#1) (-216#64) s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect s := by
  have fetched := body_codeAt code op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, next, branch, compare64, compare32, greater,
       exec_inst, state_simp_rules, bitvec_rules, minimal_theory, apply_ite]
  case p548 =>
    by_cases n : r (.FLAG .N) s = r (.FLAG .V) s <;>
      by_cases z : r (.FLAG .Z) s = 0#1 <;> simp_all
  all_goals split <;> simp_all

@[simp] theorem Op.program (op : Op) (s : ArmState) : (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, next, branch, compare64, compare32, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) : read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, next, branch, compare64, compare32, state_simp_rules]

@[simp] theorem Op.memory (op : Op) (s : ArmState) : (op.effect s).mem = s.mem := by
  cases op <;> simp [Op.effect, next, branch, compare64, compare32, state_simp_rules]

@[simp] theorem Op.register (op : Op) (s : ArmState) (reg : BitVec 5) :
    r (.GPR reg) (op.effect s) = r (.GPR reg) s := by
  cases op <;> simp [Op.effect, next, branch, compare64, compare32, state_simp_rules]

@[simp] theorem Op.vector (op : Op) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (op.effect s) = r (.SFP reg) s := by
  cases op <;> simp [Op.effect, next, branch, compare64, compare32, state_simp_rules]

def block (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      Follows base ops (op.effect s)

theorem runs (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (follows : Follows base ops s) : run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops induction =>
    change run (ops.length + 1) s = block ops (op.effect s)
    rw [run, step op s base code error follows.1]
    exact induction _ (by simpa only [CodeAt, Op.program] using code)
      ((op.error s).trans error) follows.2

@[simp] theorem block_program (ops : List Op) (s : ArmState) : (block ops s).program = s.program := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.program s)

@[simp] theorem block_error (ops : List Op) (s : ArmState) : read_err (block ops s) = read_err s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.error s)

@[simp] theorem block_memory (ops : List Op) (s : ArmState) : (block ops s).mem = s.mem := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.memory s)

@[simp] theorem block_register (ops : List Op) (s : ArmState) (reg : BitVec 5) :
    r (.GPR reg) (block ops s) = r (.GPR reg) s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.register s reg)

@[simp] theorem block_vector (ops : List Op) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (block ops s) = r (.SFP reg) s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.vector s reg)

end SszArm.Emit.Dispatch

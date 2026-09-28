import SszArm.EmitContract

namespace SszArm.Emit.Activation

inductive Op where
  | p0 | p4 | p8 | p12 | p16 | p20 | p24 | p28 | p32 | p36 | p40 | p44
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p0 => (0, 0xd10283ff#32)
  | .p4 => (4, 0xa9056ffe#32)
  | .p8 => (8, 0xa90667fa#32)
  | .p12 => (12, 0xa9075ff8#32)
  | .p16 => (16, 0xa90857f6#32)
  | .p20 => (20, 0xa9094ff4#32)
  | .p24 => (24, 0xf9400028#32)
  | .p28 => (28, 0x39400049#32)
  | .p32 => (32, 0xaa0503f5#32)
  | .p36 => (36, 0xaa0403f4#32)
  | .p40 => (40, 0xaa0203f6#32)
  | .p44 => (44, 0xaa0003f3#32)

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

def save (first second : BitVec 5) (offset : BitVec 64) (s : ArmState) : ArmState :=
  next (write_mem_bytes 16 (r (.GPR 31#5) s + offset)
    (r (.GPR second) s ++ r (.GPR first) s) s)

def Op.effect : Op → ArmState → ArmState
  | .p0, s => put 31 (r (.GPR 31#5) s - 160#64) s
  | .p4, s => save 30 27 80#64 s
  | .p8, s => save 26 25 96#64 s
  | .p12, s => save 24 23 112#64 s
  | .p16, s => save 22 21 128#64 s
  | .p20, s => save 20 19 144#64 s
  | .p24, s => put 8 (read_mem_bytes 8 (r (.GPR 1#5) s) s) s
  | .p28, s => put 9 ((read_mem_bytes 1 (r (.GPR 2#5) s) s).setWidth 64) s
  | .p32, s => put 21 (r (.GPR 5#5) s) s
  | .p36, s => put 20 (r (.GPR 4#5) s) s
  | .p40, s => put 22 (r (.GPR 2#5) s) s
  | .p44, s => put 19 (r (.GPR 0#5) s) s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) : stepi s = op.effect s := by
  have fetched := body_codeAt code op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, next, put, save, exec_inst, state_simp_rules, bitvec_rules,
       minimal_theory, aligned, BitVec.sub_eq_add_neg, BitVec.setWidth_eq]
  all_goals exact w_of_w_commute (by decide)

@[simp] theorem Op.program (op : Op) (s : ArmState) : (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, next, put, save, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) : read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, next, put, save, state_simp_rules]

def block (ops : List Op) (s : ArmState) : ArmState := ops.foldl (fun t op => op.effect t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => CheckSPAlignment s ∧
      read_pc s = base + BitVec.ofNat 64 op.row.1 ∧ Follows base ops (op.effect s)

theorem runs (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (follows : Follows base ops s) : run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops induction =>
    change run (ops.length + 1) s = block ops (op.effect s)
    rw [run, step op s base code error follows.1 follows.2.1]
    exact induction _ (by simpa only [CodeAt, Op.program] using code)
      ((op.error s).trans error) follows.2.2

end SszArm.Emit.Activation

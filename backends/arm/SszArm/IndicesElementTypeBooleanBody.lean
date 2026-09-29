import SszArm.IndicesElementTypeReturn

set_option autoImplicit false

namespace SszArm.Indices.ElementType.BooleanBody

inductive Op where
  | p60 | p64 | p68 | p72 | p76 | p80 | p84 | p88 | p92 | p96 | p100 | p104 | p108 | p112 | p116 | p120 | p124 | p128 | p132
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p60 => (60, 0xd10043ff#32)
  | .p64 => (64, 0xf90003e9#32)
  | .p68 => (68, 0xf90007ea#32)
  | .p72 => (72, 0x91000009#32)
  | .p76 => (76, 0xd280000a#32)
  | .p80 => (80, 0xf900012a#32)
  | .p84 => (84, 0xf94007ea#32)
  | .p88 => (88, 0xf94003e9#32)
  | .p92 => (92, 0x910043ff#32)
  | .p96 => (96, 0xd10043ff#32)
  | .p100 => (100, 0xf90003e9#32)
  | .p104 => (104, 0xf90007ea#32)
  | .p108 => (108, 0x91000009#32)
  | .p112 => (112, 0x91010129#32)
  | .p116 => (116, 0x5280000a#32)
  | .p120 => (120, 0xb900012a#32)
  | .p124 => (124, 0xf94007ea#32)
  | .p128 => (128, 0xf94003e9#32)
  | .p132 => (132, 0x910043ff#32)

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

def Op.effect : Op → ArmState → ArmState
  | .p60, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p64, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p68, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p72, s => put 9 (r (.GPR 0#5) s) s
  | .p76, s => put 10 0#64 s
  | .p80, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p84, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s
  | .p88, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p92, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p96, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p100, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p104, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p108, s => put 9 (r (.GPR 0#5) s) s
  | .p112, s => put 9 (r (.GPR 9#5) s + 64#64) s
  | .p116, s => put 10 0#64 s
  | .p120, s => next (write_mem_bytes 4 (r (.GPR 9#5) s) ((r (.GPR 10#5) s).setWidth 32) s)
  | .p124, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s
  | .p128, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p132, s => put 31 (r (.GPR 31#5) s + 16#64) s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.ElementType.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) : stepi s = op.effect s := by
  have fetched := Linked.ElementType.chunk0_codeAt code op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, next, put, exec_inst, state_simp_rules, bitvec_rules,
       minimal_theory, aligned, BitVec.sub_eq_add_neg, BitVec.setWidth_eq]
  all_goals first | rfl | exact w_of_w_commute (by decide)

@[simp] theorem Op.program (op : Op) (s : ArmState) :
    (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, next, put, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) :
    read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, next, put, state_simp_rules]

private theorem aligned_sub16 (x : BitVec 64) (aligned : Aligned x 4) :
    Aligned (x - 16#64) 4 := by
  simp only [Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat, BitVec.toNat_sub] at *
  omega

private theorem aligned_add16 (x : BitVec 64) (aligned : Aligned x 4) :
    Aligned (x + 16#64) 4 := by
  simp only [Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat, BitVec.toNat_add] at *
  omega

theorem Op.aligned (op : Op) (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (op.effect s) := by
  have start : Aligned (r (.GPR 31#5) s) 4 := by
    simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq] using aligned
  have lower := aligned_sub16 _ start
  have upper := aligned_add16 _ start
  cases op <;>
    simp only [Op.effect, next, put, CheckSPAlignment, read_gpr,
      BitVec.setWidth_eq, state_simp_rules]
  all_goals first | exact lower | exact upper | exact start

def block (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      Follows base ops (op.effect s)

theorem block_run (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.ElementType.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (follows : Follows base ops s) :
    run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops induction =>
      change run (ops.length + 1) s = block ops (op.effect s)
      rw [run, step op s base code error aligned follows.1]
      exact induction _ (Codec.Linked.WordsAt.preserve code (op.program s))
        ((op.error s).trans error) (op.aligned s aligned) follows.2

def ops : List Op := [.p60, .p64, .p68, .p72, .p76, .p80, .p84, .p88, .p92, .p96, .p100, .p104, .p108, .p112, .p116, .p120, .p124, .p128, .p132]

theorem body_run (s : ArmState) (base : BitVec 64)
    (code : Linked.ElementType.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 60#64) :
    run 19 s = block ops s := by
  apply block_run ops s base code error aligned
  change r .PC s = _ at pc
  simp (config := {decide := true}) [Follows, ops, Op.row, Op.effect, next, put,
    state_simp_rules, pc, BitVec.add_assoc]

end SszArm.Indices.ElementType.BooleanBody

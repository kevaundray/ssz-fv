import SszArm.EmitActivationEntry

namespace SszArm.Emit.ReturnBlock

open Activation (next put)

inductive Op where
  | p1004 | p1008 | p1012 | p1016 | p1020 | p1024 | p1028 | p1032 | p1036 | p1040
  | p1044 | p1048 | p1052 | p1056 | p1060 | p1064 | p1068
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p1004 => (1004, 0xd10043ff#32)
  | .p1008 => (1008, 0xf90003e9#32)
  | .p1012 => (1012, 0xf90007ea#32)
  | .p1016 => (1016, 0x91000269#32)
  | .p1020 => (1020, 0x91010129#32)
  | .p1024 => (1024, 0x5280000a#32)
  | .p1028 => (1028, 0xb900012a#32)
  | .p1032 => (1032, 0xf94007ea#32)
  | .p1036 => (1036, 0xf94003e9#32)
  | .p1040 => (1040, 0x910043ff#32)
  | .p1044 => (1044, 0xa9494ff4#32)
  | .p1048 => (1048, 0xa94857f6#32)
  | .p1052 => (1052, 0xa9475ff8#32)
  | .p1056 => (1056, 0xa94667fa#32)
  | .p1060 => (1060, 0xa9456ffe#32)
  | .p1064 => (1064, 0x910283ff#32)
  | .p1068 => (1068, 0xd65f03c0#32)

def restore (first second : BitVec 5) (offset : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR second) (read_mem_bytes 8 (r (.GPR 31#5) s + offset + 8#64) s)
    (put first (read_mem_bytes 8 (r (.GPR 31#5) s + offset) s) s)

def Op.effect : Op → ArmState → ArmState
  | .p1004, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p1008, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p1012, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p1016, s => put 9 (r (.GPR 19#5) s) s
  | .p1020, s => put 9 (r (.GPR 9#5) s + 64#64) s
  | .p1024, s => put 10 0#64 s
  | .p1028, s => next (write_mem_bytes 4 (r (.GPR 9#5) s) ((r (.GPR 10#5) s).setWidth 32) s)
  | .p1032, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s
  | .p1036, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p1040, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p1044, s => restore 20 19 144#64 s
  | .p1048, s => restore 22 21 128#64 s
  | .p1052, s => restore 24 23 112#64 s
  | .p1056, s => restore 26 25 96#64 s
  | .p1060, s => restore 30 27 80#64 s
  | .p1064, s => put 31 (r (.GPR 31#5) s + 160#64) s
  | .p1068, s => w .PC (r (.GPR 30#5) s) s

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
      [Op.effect, next, put, restore, exec_inst, state_simp_rules, bitvec_rules,
       minimal_theory, aligned, BitVec.sub_eq_add_neg, BitVec.setWidth_eq,
       BoolCodec.pair_read_low, BoolCodec.pair_read_high, BitVec.add_assoc]
  all_goals first | exact w_of_w_commute (by decide) |
    simp only [w, write_base_pc, write_base_gpr]

@[simp] theorem Op.program (op : Op) (s : ArmState) : (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, next, put, restore, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) : read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, next, put, restore, state_simp_rules]

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

end SszArm.Emit.ReturnBlock

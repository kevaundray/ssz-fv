import SszArm.MeasureActivationPrologue

namespace SszArm.Measure.ReturnBlock

open Activation (next put)

inductive Op where
  | p4116 | p4120 | p4124 | p4128 | p4132 | p4136 | p4140
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p4116 => (4116, 0xa9504ff4#32)
  | .p4120 => (4120, 0xa94f57f6#32)
  | .p4124 => (4124, 0xa94e5ff8#32)
  | .p4128 => (4128, 0xa94d67fa#32)
  | .p4132 => (4132, 0xa94c7bfd#32)
  | .p4136 => (4136, 0x910443ff#32)
  | .p4140 => (4140, 0xd65f03c0#32)

def restore (first second : BitVec 5) (offset : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR second) (read_mem_bytes 8 (r (.GPR 31#5) s + offset + 8#64) s)
    (put first (read_mem_bytes 8 (r (.GPR 31#5) s + offset) s) s)

def Op.effect : Op → ArmState → ArmState
  | .p4116, s => restore 20 19 256#64 s
  | .p4120, s => restore 22 21 240#64 s
  | .p4124, s => restore 24 23 224#64 s
  | .p4128, s => restore 26 25 208#64 s
  | .p4132, s => restore 29 30 192#64 s
  | .p4136, s => put 31 (r (.GPR 31#5) s + 272#64) s
  | .p4140, s => w .PC (r (.GPR 30#5) s) s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) : stepi s = op.effect s := by
  have fetched := body_codeAt code op.row (by
    cases op <;> simp only [bodyProgram, List.mem_append] <;> decide)
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, next, put, restore, exec_inst, state_simp_rules, bitvec_rules,
       minimal_theory, aligned, BitVec.setWidth_eq,
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
    exact induction _ (code.congr (op.program s)) ((op.error s).trans error) follows.2.2

end SszArm.Measure.ReturnBlock

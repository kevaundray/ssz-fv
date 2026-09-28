import SszArm.EmitContract

namespace SszArm.Emit.Scalar

inductive Op where
  | p344 | p796 | p800 | p804 | p808 | p812 | p816
  | p820 | p824 | p828 | p832 | p836 | p840 | p844 | p848 | p852 | p860 | p864
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p344 => (344, 0x34000e29#32)
  | .p796 => (796, 0xb4002475#32)
  | .p800 => (800, 0x394006c8#32)
  | .p804 => (804, 0x52800029#32)
  | .p808 => (808, 0xf9000269#32)
  | .p812 => (812, 0x39000288#32)
  | .p816 => (816, 0x1400002f#32)
  | .p820 => (820, 0x927f0908#32)
  | .p824 => (824, 0xf100091f#32)
  | .p828 => (828, 0x54fff101#32)
  | .p832 => (832, 0xf9400ad7#32)
  | .p836 => (836, 0xeb1502ff#32)
  | .p840 => (840, 0x54002208#32)
  | .p844 => (844, 0xf94006c1#32)
  | .p848 => (848, 0xaa1403e0#32)
  | .p852 => (852, 0xaa1703e2#32)
  | .p860 => (860, 0xf9000277#32)
  | .p864 => (864, 0x14000023#32)

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

def Op.effect (op : Op) (s : ArmState) : ArmState :=
  match op with
  | .p344 => w .PC (read_pc s + if (r (.GPR 9#5) s).setWidth 32 = 0#32 then 452#64 else 4#64) s
  | .p796 => w .PC (read_pc s + if r (.GPR 21#5) s = 0#64 then 1164#64 else 4#64) s
  | .p800 => put 8 ((read_mem_bytes 1 (r (.GPR 22#5) s + 1#64) s).setWidth 64) s
  | .p804 => put 9 1#64 s
  | .p808 => next (write_mem_bytes 8 (r (.GPR 19#5) s) (r (.GPR 9#5) s) s)
  | .p812 => next (write_mem_bytes 1 (r (.GPR 20#5) s) ((r (.GPR 8#5) s).setWidth 8) s)
  | .p816 => w .PC (read_pc s + 188#64) s
  | .p820 => put 8 (r (.GPR 8#5) s &&& 14#64) s
  | .p824 => write_pstate (AddWithCarry (r (.GPR 8#5) s) (~~~2#64) 1#1).2 (next s)
  | .p828 => w .PC (read_pc s + if r (.FLAG .Z) s ≠ 1#1 then -480#64 else 4#64) s
  | .p832 => put 23 (read_mem_bytes 8 (r (.GPR 22#5) s + 16#64) s) s
  | .p836 => write_pstate (AddWithCarry (r (.GPR 23#5) s) (~~~r (.GPR 21#5) s) 1#1).2 (next s)
  | .p840 => w .PC (read_pc s + if r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s ≠ 1#1 then 1088#64 else 4#64) s
  | .p844 => put 1 (read_mem_bytes 8 (r (.GPR 22#5) s + 8#64) s) s
  | .p848 => put 0 (r (.GPR 20#5) s) s
  | .p852 => put 2 (r (.GPR 23#5) s) s
  | .p860 => next (write_mem_bytes 8 (r (.GPR 19#5) s) (r (.GPR 23#5) s) s)
  | .p864 => w .PC (read_pc s + 140#64) s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) : stepi s = op.effect s := by
  have fetched := body_codeAt code op.row (by cases op <;> decide)
  have zero : r (.FLAG .Z) s ≠ 1#1 ↔ r (.FLAG .Z) s = 0#1 := by bv_omega
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned, zero]
  all_goals first | rfl | exact w_of_w_commute (by decide) | (split <;> simp_all)

@[simp] theorem Op.program (op : Op) (s : ArmState) : (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, put, next, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) : read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, put, next, state_simp_rules]

@[simp] theorem Op.stack (op : Op) (s : ArmState) :
    r (.GPR 31#5) (op.effect s) = r (.GPR 31#5) s := by
  cases op <;> simp [Op.effect, put, next, state_simp_rules]

def block (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧ Follows base ops (op.effect s)

theorem runs (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (follows : Follows base ops s) : run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops induction =>
    change run (ops.length + 1) s = block ops (op.effect s)
    rw [run, step op s base code error aligned follows.1]
    exact induction _ (by simpa only [CodeAt, Op.program] using code)
      ((op.error s).trans error)
      (by simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, Op.stack] using aligned)
      follows.2

end SszArm.Emit.Scalar

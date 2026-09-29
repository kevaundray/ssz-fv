import SszArm.IndicesRebaseWords
import SszArm.DispatchBlocks
import SszArm.BoolMemory
import SszArm.BoolAlignment

set_option autoImplicit false

namespace SszArm.Indices.Rebase.Count

open Dispatch.Block (next put branch)

inductive Op where
  | p12 | p16 | p20 | p24 | p28 | p32 | p36 | p40 | p44 | p48 | p52 | p56
  | p60 | p64 | p68 | p72 | p76 | p80 | p84 | p88 | p92 | p96 | p100
  | p304 | p308 | p312
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p12 => (12, 0xb1000489#32)
  | .p16 => (16, 0x54000062#32)
  | .p20 => (20, 0xaa0503e8#32)
  | .p24 => (24, 0x14000002#32)
  | .p28 => (28, 0x910004a8#32)
  | .p32 => (32, 0xf240153f#32)
  | .p36 => (36, 0xd10043ff#32)
  | .p40 => (40, 0xf90003eb#32)
  | .p44 => (44, 0xd346fd2b#32)
  | .p48 => (48, 0xaa08e96a#32)
  | .p52 => (52, 0xf94003eb#32)
  | .p56 => (56, 0x910043ff#32)
  | .p60 => (60, 0xd346fd0b#32)
  | .p64 => (64, 0x54000061#32)
  | .p68 => (68, 0x5280000c#32)
  | .p72 => (72, 0x14000002#32)
  | .p76 => (76, 0x5280002c#32)
  | .p80 => (80, 0xab0c014a#32)
  | .p84 => (84, 0x54000062#32)
  | .p88 => (88, 0xaa0b03eb#32)
  | .p92 => (92, 0x14000002#32)
  | .p96 => (96, 0x9100056b#32)
  | .p100 => (100, 0xb400066b#32)
  | .p304 => (304, 0xb40006aa#32)
  | .p308 => (308, 0xf100055f#32)
  | .p312 => (312, 0x54000921#32)

def Op.effect : Op → ArmState → ArmState
  | .p12, s => Udivti3.flagged 9 (r (.GPR 4#5) s) 1#64 0#1 s
  | .p16, s | .p84, s => branch (r (.FLAG .C) s = 1#1) 12#64 s
  | .p20, s => put 8 (r (.GPR 5#5) s) s
  | .p24, s | .p72, s | .p92, s => w .PC (read_pc s + 8#64) s
  | .p28, s => put 8 (r (.GPR 5#5) s + 1#64) s
  | .p32, s => write_pstate (DPI.update_logical_imm_pstate (r (.GPR 9#5) s &&& 63#64)) (next s)
  | .p36, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p40, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 11#5) s) s)
  | .p44, s => put 11 (r (.GPR 9#5) s >>> (6 : Nat)) s
  | .p48, s => put 10 (r (.GPR 11#5) s ||| (r (.GPR 8#5) s <<< (58 : Nat))) s
  | .p52, s => put 11 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p56, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p60, s => put 11 (r (.GPR 8#5) s >>> (6 : Nat)) s
  | .p64, s => branch (r (.FLAG .Z) s ≠ 1#1) 12#64 s
  | .p68, s => put 12 0#64 s
  | .p76, s => put 12 1#64 s
  | .p80, s => Udivti3.flagged 10 (r (.GPR 10#5) s) (r (.GPR 12#5) s) 0#1 s
  | .p88, s => put 11 (r (.GPR 11#5) s) s
  | .p96, s => put 11 (r (.GPR 11#5) s + 1#64) s
  | .p100, s => branch (r (.GPR 11#5) s = 0#64) 204#64 s
  | .p304, s => branch (r (.GPR 10#5) s = 0#64) 212#64 s
  | .p308, s => Udivti3.compare (r (.GPR 10#5) s) 1#64 s
  | .p312, s => branch (r (.FLAG .Z) s ≠ 1#1) 292#64 s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.Rebase.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (entry : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect s := by
  have fetched := code op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [Op.row] at entry fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error entry
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, next, put, branch, Udivti3.flagged, Udivti3.compare, Udivti3.next,
       exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned,
       BitVec.sub_eq_add_neg, BitVec.add_assoc, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

@[simp] theorem Op.program (op : Op) (s : ArmState) :
    (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, next, put, branch, Udivti3.flagged, Udivti3.compare,
    Udivti3.next, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) :
    read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, next, put, branch, Udivti3.flagged, Udivti3.compare,
    Udivti3.next, state_simp_rules]

@[simp] theorem Op.vector (op : Op) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (op.effect s) = r (.SFP reg) s := by
  cases op <;> simp [Op.effect, next, put, branch, Udivti3.flagged, Udivti3.compare,
    Udivti3.next, state_simp_rules]

def Op.stackValue : Op → BitVec 64 → BitVec 64
  | .p36, sp => sp - 16#64
  | .p56, sp => sp + 16#64
  | _, sp => sp

@[simp] theorem Op.sp (op : Op) (s : ArmState) :
    r (.GPR 31#5) (op.effect s) = op.stackValue (r (.GPR 31#5) s) := by
  cases op <;> simp [Op.effect, Op.stackValue, next, put, branch, Udivti3.flagged,
    Udivti3.compare, Udivti3.next, state_simp_rules]

theorem Op.aligned (op : Op) (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (op.effect s) := by
  apply CheckSPAlignment_of_r_sp_aligned (op.sp s)
  have original := BoolCodec.stack_aligned s aligned
  cases op <;> simp only [Op.stackValue]
  all_goals first
    | exact original
    | exact BoolCodec.aligned_sub16 _ original
    | exact BoolCodec.aligned_add16 _ original

def block (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect t) s

def ControlFlow (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      ControlFlow base ops (op.effect s)

theorem block_run (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.Rebase.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (control : ControlFlow base ops s) :
    run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = block ops (op.effect s)
    rw [run, step op s base code error aligned control.1]
    exact ih _ (Codec.Linked.WordsAt.preserve code (op.program s))
      ((op.error s).trans error) (op.aligned s aligned) control.2

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

@[simp] theorem block_vector (ops : List Op) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (block ops s) = r (.SFP reg) s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.vector s reg)

theorem block_aligned (ops : List Op) (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (block ops s) := by
  induction ops generalizing s with
  | nil => exact aligned
  | cons op ops ih => exact ih _ (op.aligned s aligned)

end SszArm.Indices.Rebase.Count

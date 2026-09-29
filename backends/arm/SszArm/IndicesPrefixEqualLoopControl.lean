import SszArm.IndicesLinkedPrefixEqual
import SszArm.Udivti3Arithmetic
import SszArm.DelimitedMemory

namespace SszArm.Indices.PrefixEqual.LoopControl

open Udivti3 (put next flagged compare)

inductive Op where
  | p704 | p708 | p712 | p716 | p720 | p724 | p728 | p732 | p736
  | p740 | p744 | p748 | p752 | p756 | p760 | p764
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p704 => (704, 0x14000009#32)
  | .p708 => (708, 0xaa1f03e7#32)
  | .p712 => (712, 0xb10005ad#32)
  | .p716 => (716, 0x91002252#32)
  | .p720 => (720, 0x91002042#32)
  | .p724 => (724, 0x1a8433f3#32)
  | .p728 => (728, 0xca130063#32)
  | .p732 => (732, 0xeb07007f#32)
  | .p736 => (736, 0x54fffbe1#32)
  | .p740 => (740, 0x8b0d0223#32)
  | .p744 => (744, 0xb100047f#32)
  | .p748 => (748, 0x540018a0#32)
  | .p752 => (752, 0x8b0d01c3#32)
  | .p756 => (756, 0x91000467#32)
  | .p760 => (760, 0xeb0e00ff#32)
  | .p764 => (764, 0x540008c3#32)

def Op.effect (base : BitVec 64) : Op → ArmState → ArmState
  | .p704, s => w .PC (base + 740#64) s
  | .p708, s => put 7 0#64 s
  | .p712, s => flagged 13 (r (.GPR 13#5) s) 1#64 0#1 s
  | .p716, s => put 18 (r (.GPR 18#5) s + 8#64) s
  | .p720, s => put 2 (r (.GPR 2#5) s + 8#64) s
  | .p724, s => put 19 (if r (.FLAG .C) s = 1#1 then
      ((r (.GPR 4#5) s).setWidth 32).setWidth 64 else 0#64) s
  | .p728, s => put 3 (r (.GPR 3#5) s ^^^ r (.GPR 19#5) s) s
  | .p732, s => compare (r (.GPR 3#5) s) (r (.GPR 7#5) s) s
  | .p736, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 740#64 else base + 604#64) s
  | .p740, s => put 3 (r (.GPR 17#5) s + r (.GPR 13#5) s) s
  | .p744, s => write_pstate (AddWithCarry (r (.GPR 3#5) s) 1#64 0#1).2 (next s)
  | .p748, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 1536#64 else base + 752#64) s
  | .p752, s => put 3 (r (.GPR 14#5) s + r (.GPR 13#5) s) s
  | .p756, s => put 7 (r (.GPR 3#5) s + 1#64) s
  | .p760, s => compare (r (.GPR 7#5) s) (r (.GPR 14#5) s) s
  | .p764, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 768#64 else base + 1044#64) s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.PrefixEqual.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect base s := by
  have fetched := Linked.PrefixEqual.chunk2_codeAt code op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, put, next, flagged, compare, exec_inst, state_simp_rules, bitvec_rules,
        minimal_theory, pc, BitVec.add_assoc, apply_ite]
  all_goals first | rfl | exact w_of_w_commute (by decide) | (split <;> simp_all)

@[simp] theorem Op.program (op : Op) (base : BitVec 64) (s : ArmState) :
    (op.effect base s).program = s.program := by
  cases op <;> simp [Op.effect, put, next, flagged, compare, state_simp_rules]

@[simp] theorem Op.error (op : Op) (base : BitVec 64) (s : ArmState) :
    read_err (op.effect base s) = read_err s := by
  cases op <;> simp [Op.effect, put, next, flagged, compare, state_simp_rules]

@[simp] theorem Op.memory (op : Op) (base : BitVec 64) (s : ArmState) :
    (op.effect base s).mem = s.mem := by
  cases op <;> simp [Op.effect, put, next, flagged, compare, state_simp_rules]

def block (base : BitVec 64) (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect base t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: rest, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      Follows base rest (op.effect base s)

theorem block_run (base : BitVec 64) (ops : List Op) (s : ArmState)
    (code : Linked.PrefixEqual.CodeAt s base) (error : read_err s = .None)
    (follows : Follows base ops s) : run ops.length s = block base ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih =>
      change run (rest.length + 1) s = block base rest (op.effect base s)
      rw [run, step op s base code error follows.1]
      exact ih _ (Codec.Linked.WordsAt.preserve code (op.program base s))
        ((op.error base s).trans error) follows.2

def compareOps : List Op := [.p712, .p716, .p720, .p724, .p728, .p732, .p736]
def guardOps : List Op := [.p740, .p744, .p748]
def indexOps : List Op := [.p752, .p756, .p760, .p764]

theorem compare_run (s : ArmState) (base : BitVec 64)
    (code : Linked.PrefixEqual.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 712#64) : run 7 s = block base compareOps s := by
  apply block_run base compareOps s code error
  simp [compareOps, Follows, Op.row, Op.effect, put, next, flagged, compare,
    state_simp_rules, pc, BitVec.add_assoc]

theorem guard_run (s : ArmState) (base : BitVec 64)
    (code : Linked.PrefixEqual.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 740#64) : run 3 s = block base guardOps s := by
  apply block_run base guardOps s code error
  simp [guardOps, Follows, Op.row, Op.effect, put, next, flagged, compare,
    state_simp_rules, pc, BitVec.add_assoc]

theorem index_run (s : ArmState) (base : BitVec 64)
    (code : Linked.PrefixEqual.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 752#64) : run 4 s = block base indexOps s := by
  apply block_run base indexOps s code error
  simp [indexOps, Follows, Op.row, Op.effect, put, next, flagged, compare,
    state_simp_rules, pc, BitVec.add_assoc]

@[simp] theorem block_memory (base : BitVec 64) (ops : List Op) (s : ArmState) :
    (block base ops s).mem = s.mem := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih => exact (ih _).trans (op.memory base s)

end SszArm.Indices.PrefixEqual.LoopControl

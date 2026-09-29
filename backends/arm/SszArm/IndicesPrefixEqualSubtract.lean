import SszArm.IndicesLinkedPrefixEqual
import SszArm.IndicesShiftXorArithmetic
import SszArm.DelimitedMemory

namespace SszArm.Indices.PrefixEqual.Subtract

open Udivti3 (next put flagged join)

inductive Op where
  | p200 | p204 | p208 | p212 | p216
  | p416 | p420 | p424 | p428
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p200 => (200, 0xeb020169#32)
  | .p204 => (204, 0xa9412fea#32)
  | .p208 => (208, 0xfa030188#32)
  | .p212 => (212, 0x9a8833e8#32)
  | .p216 => (216, 0x9a8933e9#32)
  | .p416 => (416, 0xeb0a01ec#32)
  | .p420 => (420, 0xfa0b020d#32)
  | .p424 => (424, 0x9a8d33ed#32)
  | .p428 => (428, 0x9a8c33ec#32)

def Op.effect : Op → ArmState → ArmState
  | .p200, s => flagged 9 (r (.GPR 11#5) s) (~~~r (.GPR 2#5) s) 1#1 s
  | .p204, s =>
      w (.GPR 11#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 24#64) s)
        (w (.GPR 10#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 16#64) s) (next s))
  | .p208, s => flagged 8 (r (.GPR 12#5) s) (~~~r (.GPR 3#5) s) (r (.FLAG .C) s) s
  | .p212, s => put 8 (if r (.FLAG .C) s = 1#1 then r (.GPR 8#5) s else 0#64) s
  | .p216, s => put 9 (if r (.FLAG .C) s = 1#1 then r (.GPR 9#5) s else 0#64) s
  | .p416, s => flagged 12 (r (.GPR 15#5) s) (~~~r (.GPR 10#5) s) 1#1 s
  | .p420, s => flagged 13 (r (.GPR 16#5) s) (~~~r (.GPR 11#5) s) (r (.FLAG .C) s) s
  | .p424, s => put 13 (if r (.FLAG .C) s = 1#1 then r (.GPR 13#5) s else 0#64) s
  | .p428, s => put 12 (if r (.FLAG .C) s = 1#1 then r (.GPR 12#5) s else 0#64) s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.PrefixEqual.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect s := by
  have fetched := code op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, flagged, next, put, exec_inst, state_simp_rules, bitvec_rules,
        minimal_theory, aligned, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
        BitVec.add_assoc, apply_ite]
  all_goals first | rfl | exact w_of_w_commute (by decide) | (split <;> simp_all)

@[simp] theorem Op.program (op : Op) (s : ArmState) : (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, flagged, next, put, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) : read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, flagged, next, put, state_simp_rules]

@[simp] theorem Op.sp (op : Op) (s : ArmState) :
    r (.GPR 31#5) (op.effect s) = r (.GPR 31#5) s := by
  cases op <;> simp [Op.effect, flagged, next, put, state_simp_rules]

@[simp] theorem Op.pc (op : Op) (s : ArmState) : read_pc (op.effect s) = read_pc s + 4#64 := by
  cases op <;> simp [Op.effect, flagged, next, put, state_simp_rules]

def block (ops : List Op) (s : ArmState) : ArmState := ops.foldl (fun t op => op.effect t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: rest, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧ Follows base rest (op.effect s)

theorem block_run (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.PrefixEqual.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (follows : Follows base ops s) :
    run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih =>
      change run (rest.length + 1) s = block rest (op.effect s)
      rw [run, step op s base code error aligned follows.1]
      apply ih _ (Codec.Linked.WordsAt.preserve code (op.program s))
        ((op.error s).trans error) _ follows.2
      simpa only [CheckSPAlignment, state_simp_rules, Op.sp] using aligned

def leftOps : List Op := [.p200, .p204, .p208, .p212, .p216]
def rightOps : List Op := [.p416, .p420, .p424, .p428]

theorem left_run (s : ArmState) (base : BitVec 64)
    (code : Linked.PrefixEqual.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 200#64) :
    run 5 s = block leftOps s := by
  apply block_run leftOps s base code error aligned
  simp [leftOps, Follows, Op.row, pc, Op.pc, BitVec.add_assoc]

theorem right_run (s : ArmState) (base : BitVec 64)
    (code : Linked.PrefixEqual.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 416#64) :
    run 4 s = block rightOps s := by
  apply block_run rightOps s base code error aligned
  simp [rightOps, Follows, Op.row, pc, Op.pc, BitVec.add_assoc]

theorem left_value (s : ArmState) :
    join (r (.GPR 9#5) (block leftOps s)) (r (.GPR 8#5) (block leftOps s)) =
      join (r (.GPR 11#5) s) (r (.GPR 12#5) s) -
        join (r (.GPR 2#5) s) (r (.GPR 3#5) s) := by
  have value := ShiftXor.saturating_subtract (r (.GPR 11#5) s) (r (.GPR 12#5) s)
    (r (.GPR 2#5) s) (r (.GPR 3#5) s)
  simpa [block, leftOps, Op.effect, flagged, put, next, state_simp_rules,
    ShiftXor.lowSub, ShiftXor.highSub, apply_ite, join] using value

theorem right_value (s : ArmState) :
    join (r (.GPR 12#5) (block rightOps s)) (r (.GPR 13#5) (block rightOps s)) =
      join (r (.GPR 15#5) s) (r (.GPR 16#5) s) -
        join (r (.GPR 10#5) s) (r (.GPR 11#5) s) := by
  have value := ShiftXor.saturating_subtract (r (.GPR 15#5) s) (r (.GPR 16#5) s)
    (r (.GPR 10#5) s) (r (.GPR 11#5) s)
  simpa [block, rightOps, Op.effect, flagged, put, next, state_simp_rules,
    ShiftXor.lowSub, ShiftXor.highSub, apply_ite, join] using value

/-- Both width subtraction blocks are read-only, including the caller's u128
stack argument load that lies between left SUBS and SBCS. -/
theorem block_memory (ops : List Op) (s : ArmState) : (block ops s).mem = s.mem := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih =>
      change (block rest (op.effect s)).mem = s.mem
      rw [ih]
      cases op <;> simp [Op.effect, flagged, next, put, state_simp_rules]

end SszArm.Indices.PrefixEqual.Subtract

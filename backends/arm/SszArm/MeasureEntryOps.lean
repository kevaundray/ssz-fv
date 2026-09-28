import SszArm.MeasureActivationOps
import SszArm.EmitDispatchOps

namespace SszArm.Measure.Dispatch

open Emit.Dispatch (branch compare64 greater next)
open Activation (put)

inductive Op where
  | p44 | p48 | p52 | p56 | p60 | p328 | p332 | p336 | p340 | p344
  | p444 | p448 | p552 | p556 | p560 | p564
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p44 => (44, 0xf100153f#32)
  | .p48 => (48, 0x540008cd#32)
  | .p52 => (52, 0x2a0403f6#32)
  | .p56 => (56, 0xf100213f#32)
  | .p60 => (60, 0x54000c0d#32)
  | .p328 => (328, 0xf100093f#32)
  | .p332 => (332, 0x540006ec#32)
  | .p336 => (336, 0xb4000d49#32)
  | .p340 => (340, 0xf100053f#32)
  | .p344 => (344, 0x54001961#32)
  | .p444 => (444, 0xf100193f#32)
  | .p448 => (448, 0x54000760#32)
  | .p552 => (552, 0xf1000d3f#32)
  | .p556 => (556, 0x540006e0#32)
  | .p560 => (560, 0xf100113f#32)
  | .p564 => (564, 0x54001561#32)

def Op.effect : Op → ArmState → ArmState
  | .p44, s => compare64 (r (.GPR 9#5) s) 5#64 s
  | .p48, s => branch (¬ greater s) 280#64 s
  | .p52, s => put 22 (((r (.GPR 4#5) s).setWidth 32).setWidth 64) s
  | .p56, s => compare64 (r (.GPR 9#5) s) 8#64 s
  | .p60, s => branch (¬ greater s) 384#64 s
  | .p328, s => compare64 (r (.GPR 9#5) s) 2#64 s
  | .p332, s => branch (greater s) 220#64 s
  | .p336, s => branch (r (.GPR 9#5) s = 0#64) 424#64 s
  | .p340, s => compare64 (r (.GPR 9#5) s) 1#64 s
  | .p344, s => branch (r (.FLAG .Z) s ≠ 1#1) 812#64 s
  | .p444, s => compare64 (r (.GPR 9#5) s) 6#64 s
  | .p448, s => branch (r (.FLAG .Z) s = 1#1) 236#64 s
  | .p552, s => compare64 (r (.GPR 9#5) s) 3#64 s
  | .p556, s => branch (r (.FLAG .Z) s = 1#1) 220#64 s
  | .p560, s => compare64 (r (.GPR 9#5) s) 4#64 s
  | .p564, s => branch (r (.FLAG .Z) s ≠ 1#1) 684#64 s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) : stepi s = op.effect s := by
  have fetched := body_codeAt code op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, next, branch, compare64, greater, put, Activation.next,
       exec_inst, state_simp_rules, bitvec_rules, minimal_theory, apply_ite]
  case p48 =>
    by_cases n : r (.FLAG .N) s = r (.FLAG .V) s <;>
      by_cases z : r (.FLAG .Z) s = 0#1 <;> simp_all
  case p60 =>
    by_cases n : r (.FLAG .N) s = r (.FLAG .V) s <;>
      by_cases z : r (.FLAG .Z) s = 0#1 <;> simp_all
  case p332 =>
    by_cases n : r (.FLAG .N) s = r (.FLAG .V) s <;>
      by_cases z : r (.FLAG .Z) s = 0#1 <;> simp_all
  all_goals first | exact w_of_w_commute (by decide) | (split <;> simp_all)

@[simp] theorem Op.program (op : Op) (s : ArmState) : (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, next, branch, compare64, put, Activation.next, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) : read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, next, branch, compare64, put, Activation.next, state_simp_rules]

@[simp] theorem Op.memory (op : Op) (s : ArmState) : (op.effect s).mem = s.mem := by
  cases op <;> simp [Op.effect, next, branch, compare64, put, Activation.next, state_simp_rules]

@[simp] theorem Op.register (op : Op) (s : ArmState) (reg : BitVec 5) (untouched : reg ≠ 22#5) :
    r (.GPR reg) (op.effect s) = r (.GPR reg) s := by
  cases op <;> simp [Op.effect, next, branch, compare64, put, Activation.next, state_simp_rules, untouched]

@[simp] theorem Op.vector (op : Op) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (op.effect s) = r (.SFP reg) s := by
  cases op <;> simp [Op.effect, next, branch, compare64, put, Activation.next, state_simp_rules]

def block (ops : List Op) (s : ArmState) : ArmState := ops.foldl (fun t op => op.effect t) s

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
    exact induction _ (code.congr (op.program s)) ((op.error s).trans error) follows.2

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

@[simp] theorem block_register (ops : List Op) (s : ArmState) (reg : BitVec 5) (untouched : reg ≠ 22#5) :
    r (.GPR reg) (block ops s) = r (.GPR reg) s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.register s reg untouched)

@[simp] theorem block_vector (ops : List Op) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (block ops s) = r (.SFP reg) s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.vector s reg)

end SszArm.Measure.Dispatch

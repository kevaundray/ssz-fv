import SszArm.CodecLinkedPlanSingleton
import SszArm.MeasureActivationReturnOps

set_option autoImplicit false

namespace SszArm.Codec.Measure.Singleton.Activation

open SszArm.Measure.Activation (next put save)
open SszArm.Measure.ReturnBlock (restore)

inductive Exit where | success | failure deriving DecidableEq

inductive Op where
  | enter | saveLink | savePair | restorePair (site : Exit) | restoreLink (site : Exit) | ret (site : Exit)
  deriving DecidableEq

def Exit.pc : Exit → Nat | .success => 156 | .failure => 364

def Op.row : Op → Nat × BitVec 32
  | .enter => (0, 0xd10083ff#32)
  | .saveLink => (4, 0xf90003fe#32)
  | .savePair => (8, 0xa9014ff4#32)
  | .restorePair site => (site.pc, 0xa9414ff4#32)
  | .restoreLink site => (site.pc + 4, 0xf84207fe#32)
  | .ret site => (site.pc + 8, 0xd65f03c0#32)

def Op.effect : Op → ArmState → ArmState
  | .enter, s => put 31 (r (.GPR 31) s - 32#64) s
  | .saveLink, s => next (write_mem_bytes 8 (r (.GPR 31) s) (r (.GPR 30) s) s)
  | .savePair, s => save 20 19 16#64 s
  | .restorePair _, s => restore 20 19 16#64 s
  | .restoreLink _, s => w (.GPR 31) (r (.GPR 31) s + 32#64)
      (put 30 (read_mem_bytes 8 (r (.GPR 31) s) s) s)
  | .ret _, s => w .PC (r (.GPR 30) s) s

theorem row_mem (op : Op) : op.row ∈ Linked.PlanSingleton.program := by
  cases op with
  | enter | saveLink | savePair => decide
  | restorePair site | restoreLink site | ret site => cases site <;> decide

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.PlanSingleton.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect s := by
  have fetched := code op.row (row_mem op)
  cases op with
  | enter | saveLink | savePair =>
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, next, put, save, exec_inst, state_simp_rules, bitvec_rules,
       minimal_theory, aligned, BitVec.sub_eq_add_neg, BitVec.setWidth_eq]
    all_goals exact w_of_w_commute (by decide)
  | restorePair site | restoreLink site | ret site =>
    cases site <;> simp only [Op.row, Exit.pc] at pc fetched
    all_goals
      rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
        (fetch_inst_from_program.trans fetched) rfl]
      simp (config := {decide := true, instances := true})
        [Op.effect, next, put, restore, exec_inst, state_simp_rules, bitvec_rules,
         minimal_theory, aligned, BitVec.setWidth_eq,
         BoolCodec.pair_read_low, BoolCodec.pair_read_high, BitVec.add_assoc]
    all_goals first
      | exact w_of_w_commute (by decide)
      | simp only [w, write_base_pc, write_base_gpr]

@[simp] theorem Op.program (op : Op) (s : ArmState) : (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, next, put, save, restore, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) : read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, next, put, save, restore, state_simp_rules]

def block (ops : List Op) (s : ArmState) : ArmState := ops.foldl (fun t op => op.effect t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => CheckSPAlignment s ∧
      read_pc s = base + BitVec.ofNat 64 op.row.1 ∧ Follows base ops (op.effect s)

theorem runs (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.PlanSingleton.CodeAt s base) (error : read_err s = .None)
    (follows : Follows base ops s) : run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = block ops (op.effect s)
    rw [run, step op s base code error follows.1 follows.2.1]
    apply ih _ _ ((op.error s).trans error) follows.2.2
    intro row member
    simpa only [Op.program] using code row member

end SszArm.Codec.Measure.Singleton.Activation

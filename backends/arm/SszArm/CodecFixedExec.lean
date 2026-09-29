import SszArm.CodecFixedOps
import SszArm.CodecLinkedIsFixed
import SszArm.UintShifts

namespace SszArm.Codec.Fixed.IsFixed

open Dispatch.Block (next put save branch greater)
open UintCodec (uint_lsl3_mask uint_and_ones)

theorem linked_code (s : ArmState) (base : BitVec 64)
    (code : Linked.IsFixed.CodeAt s base) : CodeAt s base := by
  intro op
  exact code op.row (by cases op <;> decide)

/-- One real decoded ISA step, including the self-call and both returns. -/
theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) : stepi s = op.effect s := by
  have fetched := code op
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, next, put, save, branch, greater, loadPair, restore,
       Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules, bitvec_rules,
       minimal_theory, aligned, BitVec.sub_eq_add_neg, BitVec.add_assoc, apply_ite,
       BoolCodec.pair_read_low, BoolCodec.pair_read_high, uint_lsl3_mask, uint_and_ones]
  case p44 =>
    by_cases n : r (.FLAG .N) s = r (.FLAG .V) s <;>
      by_cases z : r (.FLAG .Z) s = 0#1 <;> simp_all
  case p48 =>
    have carry : r (.FLAG .C) s = 0#1 ∨ r (.FLAG .C) s = 1#1 := by bv_omega
    rcases carry with carry | carry <;> simp [carry]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

def block (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => CheckSPAlignment s ∧
      read_pc s = base + BitVec.ofNat 64 op.row.1 ∧ Follows base ops (op.effect s)

theorem block_run (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (follows : Follows base ops s) : run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = block ops (op.effect s)
    rw [run, step op s base code error follows.1 follows.2.1]
    exact ih _ (by simpa only [CodeAt, Op.program] using code)
      ((op.error s).trans error) follows.2.2

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

end SszArm.Codec.Fixed.IsFixed

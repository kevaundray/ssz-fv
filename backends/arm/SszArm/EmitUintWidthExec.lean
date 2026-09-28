import SszArm.EmitUintWidthOps

namespace SszArm.Emit.Uint

open UintCodec

theorem width_step (s : ArmState) (base : BitVec 64) (op : WidthOp)
    (hc : CodeAt s base) (hp : read_pc s = base + BitVec.ofNat 64 op.row.1)
    (he : read_err s = .None) (ha : CheckSPAlignment s) :
    stepi s = op.effect base s := by
  have hf := body_codeAt hc op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [WidthOp.row] at hp hf
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
      (fetch_inst_from_program.trans hf) rfl]
    change r .PC s = _ at hp
    simp (config := {decide := true, instances := true})
      [WidthOp.effect, put, next, Dispatch.next, Dispatch.compare64, Dispatch.compare32,
       exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       BoolCodec.pair_read_low, BoolCodec.pair_read_high, ha, hp, BitVec.add_assoc,
       BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all)
    | simp [w, write_base_pc, write_base_gpr]

@[simp] theorem WidthOp.program (op : WidthOp) (base : BitVec 64) (s : ArmState) :
    (op.effect base s).program = s.program := by
  cases op <;> simp [WidthOp.effect, put, next, Dispatch.next,
    Dispatch.compare64, Dispatch.compare32, state_simp_rules]

@[simp] theorem WidthOp.error (op : WidthOp) (base : BitVec 64) (s : ArmState) :
    read_err (op.effect base s) = read_err s := by
  cases op <;> simp [WidthOp.effect, put, next, Dispatch.next,
    Dispatch.compare64, Dispatch.compare32, state_simp_rules]

theorem WidthOp.aligned (op : WidthOp) (base : BitVec 64) (s : ArmState)
    (ha : CheckSPAlignment s) : CheckSPAlignment (op.effect base s) := by
  cases op <;> simp [WidthOp.effect, put, next, Dispatch.next,
    Dispatch.compare64, Dispatch.compare32, state_simp_rules, ha]
  · exact BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s ha)
  · exact BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s ha)

@[simp] theorem WidthOp.vector (op : WidthOp) (base : BitVec 64) (s : ArmState)
    (reg : BitVec 5) : r (.SFP reg) (op.effect base s) = r (.SFP reg) s := by
  cases op <;> simp [WidthOp.effect, put, next, Dispatch.next,
    Dispatch.compare64, Dispatch.compare32, state_simp_rules]

def widthBlock (base : BitVec 64) (ops : List WidthOp) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect base t) s

def WidthFollows (base : BitVec 64) : List WidthOp → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      WidthFollows base ops (op.effect base s)

theorem width_run (base : BitVec 64) (ops : List WidthOp) (s : ArmState)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : WidthFollows base ops s) : run ops.length s = widthBlock base ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = widthBlock base ops (op.effect base s)
    rw [run, width_step s base op hc hf.1 he ha]
    exact ih _ (by simpa only [CodeAt, WidthOp.program] using hc)
      ((op.error base s).trans he) (op.aligned base s ha) hf.2

@[simp] theorem widthBlock_program (base : BitVec 64) (ops : List WidthOp) (s : ArmState) :
    (widthBlock base ops s).program = s.program := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.program base s)

@[simp] theorem widthBlock_error (base : BitVec 64) (ops : List WidthOp) (s : ArmState) :
    read_err (widthBlock base ops s) = read_err s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.error base s)

end SszArm.Emit.Uint

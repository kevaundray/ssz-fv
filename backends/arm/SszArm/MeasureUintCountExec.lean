import SszArm.MeasureUintCountMasks

namespace SszArm.Measure.Uint

open UintCodec

theorem count_step (s : ArmState) (base : BitVec 64) (op : CountOp)
    (code : CodeAt s base) (pc : read_pc s = base + BitVec.ofNat 64 op.row.1)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) :
    stepi s = op.effect base s := by
  have member : op.row ∈ bodyProgram := by
    cases op <;> unfold bodyProgram
    case p416 | p420 | p424 | p428 | p432 | p436 | p440 =>
      iterate 9 apply List.mem_append_left
      apply List.mem_append_right
      decide
    all_goals
      iterate 5 apply List.mem_append_left
      apply List.mem_append_right
      decide
  have fetched := body_codeAt code op.row member
  cases op
  all_goals
    simp only [CountOp.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    change r .PC s = _ at pc
    simp (config := {decide := true, instances := true})
      [CountOp.effect, put, next, compare64, compare32, Emit.Dispatch.next,
       Emit.Dispatch.compare64, Emit.Dispatch.compare32, exec_inst, state_simp_rules,
       bitvec_rules, minimal_theory, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
       aligned, pc, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.sub_eq_add_neg,
       uint_lsl3_mask, uint_lsr3_mask, count_lsr1_mask, count_lsr58_mask,
       count_lsl6_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all)
    | simp [w, write_base_pc, write_base_gpr]

@[simp] theorem CountOp.program (op : CountOp) (base : BitVec 64) (s : ArmState) :
    (op.effect base s).program = s.program := by
  cases op <;> simp [CountOp.effect, put, next, compare32, Emit.Dispatch.compare32,
    Emit.Dispatch.next, state_simp_rules]

@[simp] theorem CountOp.error (op : CountOp) (base : BitVec 64) (s : ArmState) :
    read_err (op.effect base s) = read_err s := by
  cases op <;> simp [CountOp.effect, put, next, compare32, Emit.Dispatch.compare32,
    Emit.Dispatch.next, state_simp_rules]

theorem CountOp.aligned (op : CountOp) (base : BitVec 64) (s : ArmState)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (op.effect base s) := by
  cases op <;> simp [CountOp.effect, put, next, compare32, Emit.Dispatch.compare32,
    Emit.Dispatch.next, state_simp_rules, aligned]
  · exact BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s aligned)
  · exact BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s aligned)
  · exact BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s aligned)
  · exact BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s aligned)

@[simp] theorem CountOp.vector (op : CountOp) (base : BitVec 64) (s : ArmState)
    (reg : BitVec 5) : r (.SFP reg) (op.effect base s) = r (.SFP reg) s := by
  cases op <;> simp [CountOp.effect, put, next, compare32, Emit.Dispatch.compare32,
    Emit.Dispatch.next, state_simp_rules]

def countBlock (base : BitVec 64) (ops : List CountOp) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect base t) s

def CountFollows (base : BitVec 64) : List CountOp → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      CountFollows base ops (op.effect base s)

theorem count_run (base : BitVec 64) (ops : List CountOp) (s : ArmState)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (follows : CountFollows base ops s) : run ops.length s = countBlock base ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = countBlock base ops (op.effect base s)
    rw [run, count_step s base op code follows.1 error aligned]
    exact ih _ (code.congr (op.program base s))
      ((op.error base s).trans error) (op.aligned base s aligned) follows.2

end SszArm.Measure.Uint

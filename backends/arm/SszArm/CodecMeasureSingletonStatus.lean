import SszArm.CodecMeasureSingletonReturn
import SszArm.EmitActivationReturnStatus

set_option autoImplicit false

namespace SszArm.Codec.Measure.Singleton

open SszArm.Emit.ReturnBlock
open SszArm.Emit.Activation (next put)

/-- Only the ten status-lowering words are relocated. No nonexistent copy of
an entire emit function is assumed at the singleton instruction address. -/
def StatusCodeAt (s : ArmState) (base : BitVec 64) : Prop :=
  ∀ op ∈ SszArm.Emit.statusOps,
    s.program.find? (base + BitVec.ofNat 64 op.row.1) = some op.row.2

theorem status_code_of_linked (s : ArmState) (base : BitVec 64)
    (code : Linked.PlanSingleton.CodeAt s base) : StatusCodeAt s (base - 888#64) := by
  intro op member
  have fetched := Linked.PlanSingleton.chunk0_codeAt code
    ((op.row.1 - 888), op.row.2) (by
      cases op <;> simp only [SszArm.Emit.statusOps, List.mem_cons, List.not_mem_nil,
        or_false, reduceCtorEq, true_or, or_true] at member
      all_goals first | contradiction | decide)
  have relocated : base + BitVec.ofNat 64 (op.row.1 - 888) =
      (base - 888#64) + BitVec.ofNat 64 op.row.1 := by
    cases op <;> simp only [SszArm.Emit.statusOps, List.mem_cons, List.not_mem_nil,
      or_false, reduceCtorEq, true_or, or_true] at member
    all_goals first | contradiction | (simp only [Op.row]; bv_omega)
  rw [relocated] at fetched
  exact fetched

private theorem status_step (op : Op) (s : ArmState) (base : BitVec 64)
    (member : op ∈ SszArm.Emit.statusOps) (code : StatusCodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) : stepi s = op.effect s := by
  have fetched := code op member
  cases op <;> simp only [SszArm.Emit.statusOps, List.mem_cons, List.not_mem_nil,
    or_false, reduceCtorEq, true_or, or_true] at member
  all_goals first | contradiction |
    (simp only [Op.row] at pc fetched
     rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
       (fetch_inst_from_program.trans fetched) rfl]
     simp (config := {decide := true, instances := true})
       [Op.effect, next, put, exec_inst, state_simp_rules, bitvec_rules,
        minimal_theory, aligned, BitVec.sub_eq_add_neg, BitVec.setWidth_eq]
     all_goals first | exact w_of_w_commute (by decide) |
       simp only [w, write_base_pc, write_base_gpr])

private theorem status_runs (ops : List Op) (s : ArmState) (base : BitVec 64)
    (members : ∀ op ∈ ops, op ∈ SszArm.Emit.statusOps)
    (code : StatusCodeAt s base) (error : read_err s = .None)
    (follows : Follows base ops s) : run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = block ops (op.effect s)
    rw [run, status_step op s base (members op (by simp)) code error follows.1 follows.2.1]
    apply ih (fun next member => members next (List.mem_cons_of_mem _ member)) _
      ((op.error s).trans error) follows.2.2
    intro next member
    simpa only [Op.program] using code next member

theorem singleton_status_run (s : ArmState) (base : BitVec 64)
    (code : Linked.PlanSingleton.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 116#64) :
    run 10 s = SszArm.Emit.statusStored s := by
  have lower := BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s aligned)
  have relocated : read_pc s = (base - 888#64) + 1004#64 := by rw [pc]; bv_omega
  rw [SszArm.Emit.statusStored]
  apply status_runs SszArm.Emit.statusOps s (base - 888#64) (fun _ member => member)
    (status_code_of_linked s base code) error
  change r .PC s = (base - 888#64) + 1004#64 at relocated
  simp (config := {decide := true}) [Follows, SszArm.Emit.statusOps, Op.row,
    Op.effect, put, next, state_simp_rules, CheckSPAlignment, read_gpr,
    BitVec.setWidth_eq, relocated, BitVec.add_assoc] at aligned lower ⊢
  exact ⟨aligned, lower⟩

end SszArm.Codec.Measure.Singleton

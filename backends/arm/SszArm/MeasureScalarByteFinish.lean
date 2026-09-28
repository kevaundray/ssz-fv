import SszArm.MeasureScalarByteFrame

namespace SszArm.Measure.Scalar.Bytes

open Result
open SszNative (NatOperand)

@[irreducible] def successReady (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 4144#64) (w (.GPR 21#5) 0#64 s)

theorem success_ready_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 3744#64) : run 2 s = successReady s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base [p3744, p3748] s := by
    simp (config := {decide := true, instances := true})
      [Follows, p3744, p3748, Op.effect, exec_inst, state_simp_rules, bitvec_rules,
       minimal_theory, pc, error, BitVec.add_assoc]
  rw [show 2 = [p3744, p3748].length by rfl, runs _ s base code follows]
  simp (config := {decide := true, instances := true})
    [effect, p3744, p3748, Op.effect, exec_inst, successReady, state_simp_rules,
     bitvec_rules, minimal_theory, pc, BitVec.add_assoc, NatExact.gpr_w_pc, w_of_w_shadow]

theorem success_ready_frame (s : ArmState) (base : BitVec 64) : Frame s (successReady s base) := by
  constructor
  · simp [successReady, state_simp_rules]
  · simp [successReady, state_simp_rules]
  · simp (config := {decide := true}) [successReady, state_simp_rules]
  · simp (config := {decide := true}) [successReady, state_simp_rules]
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [successReady, state_simp_rules]
  · intro reg; simp [successReady, state_simp_rules]
  · intro address outside; simp [successReady, state_simp_rules]

@[irreducible] def vectorCompared (s : ArmState) (base : BitVec 64) : ArmState :=
  let comparison := (r (.GPR 10#5) s ^^^ r (.GPR 20#5) s) ||| r (.GPR 11#5) s
  w .PC (base + if comparison = 0#64 then 3744#64 else 3752#64)
    (w (.GPR 10#5) comparison s)

private theorem vector_xor_effect (s : ArmState) :
    p3732.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 10#5) (r (.GPR 10#5) s ^^^ r (.GPR 20#5) s) s) := by
  change exec_inst (.DPR (.Logical_shifted_reg
    { sf := 1, opc := 2, shift := 0, N := 0, Rm := 20, imm6 := 0, Rn := 10, Rd := 10 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

private theorem vector_or_effect (s : ArmState) :
    p3736.effect s = w .PC (r .PC s + 4#64)
      (w (.GPR 10#5) (r (.GPR 10#5) s ||| r (.GPR 11#5) s) s) := by
  change exec_inst (.DPR (.Logical_shifted_reg
    { sf := 1, opc := 1, shift := 0, N := 0, Rm := 11, imm6 := 0, Rn := 10, Rd := 10 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, NatExact.gpr_w_pc]

private theorem vector_branch_effect (s : ArmState) :
    p3740.effect s = w .PC
      (if r (.GPR 10#5) s = 0#64 then r .PC s + 4#64 else r .PC s + 12#64) s := by
  change exec_inst (.BR (.Compare_branch { sf := 1, op := 1, imm19 := 3, Rt := 10 })) s = _
  by_cases zero : r (.GPR 10#5) s = 0#64 <;>
    simp (config := {decide := true, instances := true})
      [exec_inst, state_simp_rules, bitvec_rules, minimal_theory, zero]

@[irreducible] private def vectorXored (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 3736#64) (w (.GPR 10#5) (r (.GPR 10#5) s ^^^ r (.GPR 20#5) s) s)

@[irreducible] private def vectorOred (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 3740#64)
    (w (.GPR 10#5) ((r (.GPR 10#5) s ^^^ r (.GPR 20#5) s) ||| r (.GPR 11#5) s) s)

private theorem vector_xored_step (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 3732#64) : p3732.effect s = vectorXored s base := by
  change r .PC s = _ at pc
  rw [vector_xor_effect, pc]
  have nextPC : base + 3732#64 + 4#64 = base + 3736#64 := by bv_omega
  rw [nextPC]
  simp only [vectorXored]

private theorem vector_ored_step (s : ArmState) (base : BitVec 64) :
    p3736.effect (vectorXored s base) = vectorOred s base := by
  have pc : r .PC (vectorXored s base) = base + 3736#64 := by
    simp only [vectorXored, r_of_w_same]
  have low : r (.GPR 10#5) (vectorXored s base) = r (.GPR 10#5) s ^^^ r (.GPR 20#5) s := by
    simp (config := {decide := true}) [vectorXored, state_simp_rules]
  have high : r (.GPR 11#5) (vectorXored s base) = r (.GPR 11#5) s := by
    simp (config := {decide := true}) [vectorXored, state_simp_rules]
  rw [vector_or_effect, pc, low, high]
  have nextPC : base + 3736#64 + 4#64 = base + 3740#64 := by bv_omega
  rw [nextPC]
  simp only [vectorXored, vectorOred, NatExact.gpr_w_pc, w_of_w_shadow]

private theorem vector_branched_step (s : ArmState) (base : BitVec 64) :
    p3740.effect (vectorOred s base) = vectorCompared s base := by
  have pc : r .PC (vectorOred s base) = base + 3740#64 := by
    simp only [vectorOred, r_of_w_same]
  have value : r (.GPR 10#5) (vectorOred s base) =
      (r (.GPR 10#5) s ^^^ r (.GPR 20#5) s) ||| r (.GPR 11#5) s := by
    simp (config := {decide := true}) [vectorOred, state_simp_rules]
  rw [vector_branch_effect, pc, value]
  have nextPC : base + 3740#64 + 4#64 = base + 3744#64 := by bv_omega
  have takenPC : base + 3740#64 + 12#64 = base + 3752#64 := by bv_omega
  rw [nextPC, takenPC]
  have distribute (condition : Prop) [Decidable condition] :
      (if condition then base + 3744#64 else base + 3752#64) =
        base + if condition then 3744#64 else 3752#64 := by split <;> rfl
  rw [distribute]
  simp only [vectorOred, vectorCompared, w_of_w_shadow]

private theorem vector_three_effects (first second third : Op) (s t u v : ArmState)
    (hfirst : first.effect s = t) (hsecond : second.effect t = u) (hthird : third.effect u = v) :
    effect [first, second, third] s = v := by
  change third.effect (second.effect (first.effect s)) = v
  exact (congrArg (fun state => third.effect (second.effect state)) hfirst).trans
    ((congrArg third.effect hsecond).trans hthird)


theorem vector_compare_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 3732#64) : run 3 s = vectorCompared s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base [p3732, p3736, p3740] s := by
    simp (config := {decide := true, instances := true})
      [Follows, p3732, p3736, p3740, Op.effect, exec_inst, state_simp_rules,
       bitvec_rules, minimal_theory, pc, error, BitVec.add_assoc]
  rw [show 3 = [p3732, p3736, p3740].length by rfl, runs _ s base code follows]
  exact vector_three_effects p3732 p3736 p3740 s (vectorXored s base) (vectorOred s base)
    (vectorCompared s base) (vector_xored_step s base pc)
    (vector_ored_step s base) (vector_branched_step s base)


theorem vector_compare_frame (s : ArmState) (base : BitVec 64) : NatNarrow.Frame s (vectorCompared s base) := by
  constructor
  · simp [vectorCompared, state_simp_rules]
  · simp [vectorCompared, state_simp_rules]
  · intro reg outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    simp (disch := simp_all) [vectorCompared, state_simp_rules]
  · intro reg; simp [vectorCompared, state_simp_rules]
  · intro address outside; simp [vectorCompared, state_simp_rules]

theorem vector_finish (s : ArmState) (base : BitVec 64) (cap : NatOperand) (size : Nat)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 3732#64) (physical : size < 2^64)
    (pointer : r (.GPR 8#5) s = cap.pointer) (payload : r (.GPR 9#5) s = cap.payload)
    (actual : r (.GPR 20#5) s = BitVec.ofNat 64 size) (fits : cap.wordCount ≤ 2)
    (low : r (.GPR 10#5) s = cap.words[0]?.getD 0#64)
    (high : r (.GPR 11#5) s = cap.words[1]?.getD 0#64) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧ Ready .vector t base cap size := by
  have equality : ((r (.GPR 10#5) s ^^^ r (.GPR 20#5) s) ||| r (.GPR 11#5) s = 0#64) ↔
      cap.value = size := by
    have semantic := (NatExact.comparison_zero cap (r (.GPR 20#5) s) _ _ fits low high).trans
      (SszNative.NatNarrow.runExact_iff cap (r (.GPR 20#5) s))
    simpa [actual, BitVec.toNat_ofNat, Nat.mod_eq_of_lt physical] using semantic
  let u := vectorCompared s base
  have hu : run 3 s = u := vector_compare_run s base code error pc
  have uf : Frame s u := Frame.of_narrow (vector_compare_frame s base)
  by_cases accepted : cap.value = size
  · have zero := equality.mpr accepted
    have up : read_pc u = base + 3744#64 := by simp [u, vectorCompared, zero, state_simp_rules]
    refine ⟨5, successReady u base, ?_, uf.trans (success_ready_frame u base), ?_⟩
    · rw [show 5 = 3 + 2 by decide, run_plus, hu]
      exact success_ready_run u base (code.congr uf.program) (uf.error.trans error) up
    · simp (config := {decide := true})
        [Ready, Kind.accepts, successReady, u, vectorCompared, state_simp_rules, accepted, actual]
  · have nonzero : (r (.GPR 10#5) s ^^^ r (.GPR 20#5) s) ||| r (.GPR 11#5) s ≠ 0#64 :=
      fun zero => accepted (equality.mp zero)
    refine ⟨3, u, hu, uf, ?_⟩
    have rejectedPC : read_pc u = base + 3752#64 := by
      simp only [u, vectorCompared, read_pc, r_of_w_same, if_neg nonzero]
    simp only [Ready, Kind.accepts, if_neg accepted]
    refine ⟨?_, rejectedPC, ?_, ?_⟩
    all_goals simp (config := {decide := true})
      [u, vectorCompared, state_simp_rules, actual, pointer, payload]

end SszArm.Measure.Scalar.Bytes

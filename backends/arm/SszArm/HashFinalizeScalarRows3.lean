import SszArm.HashFinalizeScalarRows2

namespace SszArm.Hash.Finalize

theorem scalar_p432 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [9#5] s (p432.effect s) := by
  have scalar : ScalarFrame [9#5] s (p432.effect s) := by
    constructor
    · exact p432.program s
    · simp (config := {decide := true, instances := true}) only
        [p432, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p432, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p432, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p436 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [8#5] s (p436.effect s) := by
  have scalar : ScalarFrame [8#5] s (p436.effect s) := by
    constructor
    · exact p436.program s
    · simp (config := {decide := true, instances := true}) only
        [p436, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p436, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p436, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p440 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p440.effect s) := by
  have scalar : ScalarFrame [] s (p440.effect s) := by
    constructor
    · exact p440.program s
    · simp (config := {decide := true, instances := true}) only
        [p440, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p440, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p440, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p444 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p444.effect s) := by
  exact scalar_p408 s aligned

theorem scalar_p448 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [9#5] s (p448.effect s) := by
  have scalar : ScalarFrame [9#5] s (p448.effect s) := by
    constructor
    · exact p448.program s
    · simp (config := {decide := true, instances := true}) only
        [p448, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p448, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p448, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p452 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [10#5, 11#5] s (p452.effect s) := by
  have scalar : ScalarFrame [10#5, 11#5] s (p452.effect s) := by
    constructor
    · exact p452.program s
    · simp (config := {decide := true, instances := true}) only
        [p452, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p452, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p452, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p456 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p456.effect s) := by
  have scalar : ScalarFrame [] s (p456.effect s) := by
    constructor
    · exact p456.program s
    · simp (config := {decide := true, instances := true}) only
        [p456, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p456, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p456, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p460 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p460.effect s) := by
  exact scalar_p332 s aligned

theorem scalar_p464 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [8#5] s (p464.effect s) := by
  exact scalar_p300 s aligned

theorem scalar_p468 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [11#5] s (p468.effect s) := by
  exact scalar_p384 s aligned

theorem scalar_p472 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [10#5] s (p472.effect s) := by
  exact scalar_p388 s aligned

theorem scalar_p476 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [9#5] s (p476.effect s) := by
  exact scalar_p392 s aligned

theorem scalar_p480 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [8#5] s (p480.effect s) := by
  have scalar : ScalarFrame [8#5] s (p480.effect s) := by
    constructor
    · exact p480.program s
    · simp (config := {decide := true, instances := true}) only
        [p480, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p480, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p480, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p484 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p484.effect s) := by
  exact scalar_p312 s aligned

theorem scalar_p488 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [12#5] s (p488.effect s) := by
  exact scalar_p316 s aligned

theorem scalar_p492 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p492.effect s) := by
  exact scalar_p408 s aligned

theorem scalar_p496 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [9#5] s (p496.effect s) := by
  exact scalar_p412 s aligned

theorem scalar_p500 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [11#5] s (p500.effect s) := by
  have scalar : ScalarFrame [11#5] s (p500.effect s) := by
    constructor
    · exact p500.program s
    · simp (config := {decide := true, instances := true}) only
        [p500, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p500, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p500, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p504 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p504.effect s) := by
  exact scalar_p332 s aligned

theorem scalar_p508 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [8#5] s (p508.effect s) := by
  exact scalar_p300 s aligned

theorem scalar_p512 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p512.effect s) := by
  have scalar : ScalarFrame [] s (p512.effect s) := by
    constructor
    · exact p512.program s
    · simp (config := {decide := true, instances := true}) only
        [p512, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p512, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p512, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p516 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [9#5] s (p516.effect s) := by
  exact scalar_p432 s aligned

theorem scalar_p520 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [8#5] s (p520.effect s) := by
  have scalar : ScalarFrame [8#5] s (p520.effect s) := by
    constructor
    · exact p520.program s
    · simp (config := {decide := true, instances := true}) only
        [p520, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p520, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p520, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p524 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p524.effect s) := by
  exact scalar_p440 s aligned

theorem scalar_p528 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p528.effect s) := by
  exact scalar_p408 s aligned

theorem scalar_p532 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [9#5] s (p532.effect s) := by
  exact scalar_p448 s aligned

theorem scalar_p536 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p536.effect s) := by
  have scalar : ScalarFrame [] s (p536.effect s) := by
    constructor
    · exact p536.program s
    · simp (config := {decide := true, instances := true}) only
        [p536, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p536, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p536, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p540 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p540.effect s) := by
  have scalar : ScalarFrame [] s (p540.effect s) := by
    constructor
    · exact p540.program s
    · simp (config := {decide := true, instances := true}) only
        [p540, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p540, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p540, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p544 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [19#5, 20#5] s (p544.effect s) := by
  have scalar : ScalarFrame [19#5, 20#5] s (p544.effect s) := by
    constructor
    · exact p544.program s
    · simp (config := {decide := true, instances := true}) only
        [p544, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p544, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p544, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p548 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [30#5, 31#5] s (p548.effect s) := by
  have scalar : ScalarFrame [30#5, 31#5] s (p548.effect s) := by
    constructor
    · exact p548.program s
    · simp (config := {decide := true, instances := true}) only
        [p548, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p548, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p548, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  have shifted := BoolCodec.aligned_add32 _ (BoolCodec.stack_aligned s aligned)
  simp (config := {decide := true, instances := true}) only
    [p548, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     CheckSPAlignment, aligned, shifted]
  all_goals
    have stack := BoolCodec.stack_aligned s aligned
    arm_word_nf at stack shifted ⊢
    simpa [stack] using shifted

theorem scalar_p552 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p552.effect s) := by
  have scalar : ScalarFrame [] s (p552.effect s) := by
    constructor
    · exact p552.program s
    · simp (config := {decide := true, instances := true}) only
        [p552, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p552, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p552, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

end SszArm.Hash.Finalize

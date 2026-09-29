import SszArm.HashFinalizeScalarProjection

namespace SszArm.Hash.Finalize

theorem scalar_p0 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [31#5] s (p0.effect s) := by
  have scalar : ScalarFrame [31#5] s (p0.effect s) := by
    constructor
    · exact p0.program s
    · simp (config := {decide := true, instances := true}) only
        [p0, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p0, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p0, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  have shifted := BoolCodec.aligned_sub32 _ (BoolCodec.stack_aligned s aligned)
  simp (config := {decide := true, instances := true}) only
    [p0, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     CheckSPAlignment, aligned, shifted]
  all_goals
    arm_word_nf
    exact shifted

theorem scalar_p4 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p4.effect s) := by
  have scalar : ScalarFrame [] s (p4.effect s) := by
    constructor
    · exact p4.program s
    · simp (config := {decide := true, instances := true}) only
        [p4, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p4, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p4, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p8 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p8.effect s) := by
  have scalar : ScalarFrame [] s (p8.effect s) := by
    constructor
    · exact p8.program s
    · simp (config := {decide := true, instances := true}) only
        [p8, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p8, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p8, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p12 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [8#5] s (p12.effect s) := by
  have scalar : ScalarFrame [8#5] s (p12.effect s) := by
    constructor
    · exact p12.program s
    · simp (config := {decide := true, instances := true}) only
        [p12, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p12, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p12, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p16 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p16.effect s) := by
  have scalar : ScalarFrame [] s (p16.effect s) := by
    constructor
    · exact p16.program s
    · simp (config := {decide := true, instances := true}) only
        [p16, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p16, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p16, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p20 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p20.effect s) := by
  have scalar : ScalarFrame [] s (p20.effect s) := by
    constructor
    · exact p20.program s
    · simp (config := {decide := true, instances := true}) only
        [p20, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p20, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p20, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p24 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [9#5] s (p24.effect s) := by
  have scalar : ScalarFrame [9#5] s (p24.effect s) := by
    constructor
    · exact p24.program s
    · simp (config := {decide := true, instances := true}) only
        [p24, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p24, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p24, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p28 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [31#5] s (p28.effect s) := by
  have scalar : ScalarFrame [31#5] s (p28.effect s) := by
    constructor
    · exact p28.program s
    · simp (config := {decide := true, instances := true}) only
        [p28, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p28, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p28, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  have shifted := BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s aligned)
  simp (config := {decide := true, instances := true}) only
    [p28, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     CheckSPAlignment, aligned, shifted]
  all_goals
    arm_word_nf
    exact shifted

theorem scalar_p32 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p32.effect s) := by
  have scalar : ScalarFrame [] s (p32.effect s) := by
    constructor
    · exact p32.program s
    · simp (config := {decide := true, instances := true}) only
        [p32, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p32, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p32, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p36 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [10#5] s (p36.effect s) := by
  have scalar : ScalarFrame [10#5] s (p36.effect s) := by
    constructor
    · exact p36.program s
    · simp (config := {decide := true, instances := true}) only
        [p36, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p36, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p36, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p40 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [10#5] s (p40.effect s) := by
  have scalar : ScalarFrame [10#5] s (p40.effect s) := by
    constructor
    · exact p40.program s
    · simp (config := {decide := true, instances := true}) only
        [p40, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p40, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p40, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p44 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p44.effect s) := by
  have scalar : ScalarFrame [] s (p44.effect s) := by
    constructor
    · exact p44.program s
    · simp (config := {decide := true, instances := true}) only
        [p44, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p44, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p44, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p48 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [10#5] s (p48.effect s) := by
  have scalar : ScalarFrame [10#5] s (p48.effect s) := by
    constructor
    · exact p48.program s
    · simp (config := {decide := true, instances := true}) only
        [p48, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p48, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p48, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p52 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [31#5] s (p52.effect s) := by
  have scalar : ScalarFrame [31#5] s (p52.effect s) := by
    constructor
    · exact p52.program s
    · simp (config := {decide := true, instances := true}) only
        [p52, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p52, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p52, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  have shifted := BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s aligned)
  simp (config := {decide := true, instances := true}) only
    [p52, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     CheckSPAlignment, aligned, shifted]
  all_goals
    arm_word_nf
    exact shifted

theorem scalar_p56 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [19#5] s (p56.effect s) := by
  have scalar : ScalarFrame [19#5] s (p56.effect s) := by
    constructor
    · exact p56.program s
    · simp (config := {decide := true, instances := true}) only
        [p56, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p56, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p56, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p60 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [8#5] s (p60.effect s) := by
  exact scalar_p12 s aligned

theorem scalar_p64 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [20#5] s (p64.effect s) := by
  have scalar : ScalarFrame [20#5] s (p64.effect s) := by
    constructor
    · exact p64.program s
    · simp (config := {decide := true, instances := true}) only
        [p64, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p64, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p64, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p68 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [0#5] s (p68.effect s) := by
  have scalar : ScalarFrame [0#5] s (p68.effect s) := by
    constructor
    · exact p68.program s
    · simp (config := {decide := true, instances := true}) only
        [p68, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p68, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p68, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p72 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p72.effect s) := by
  have scalar : ScalarFrame [] s (p72.effect s) := by
    constructor
    · exact p72.program s
    · simp (config := {decide := true, instances := true}) only
        [p72, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p72, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p72, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p76 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p76.effect s) := by
  have scalar : ScalarFrame [] s (p76.effect s) := by
    constructor
    · exact p76.program s
    · simp (config := {decide := true, instances := true}) only
        [p76, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p76, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p76, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p80 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p80.effect s) := by
  have scalar : ScalarFrame [] s (p80.effect s) := by
    constructor
    · exact p80.program s
    · simp (config := {decide := true, instances := true}) only
        [p80, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p80, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p80, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p84 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p84.effect s) := by
  have scalar : ScalarFrame [] s (p84.effect s) := by
    constructor
    · exact p84.program s
    · simp (config := {decide := true, instances := true}) only
        [p84, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p84, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p84, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p88 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p88.effect s) := by
  have scalar : ScalarFrame [] s (p88.effect s) := by
    constructor
    · exact p88.program s
    · simp (config := {decide := true, instances := true}) only
        [p88, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p88, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p88, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p92 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [9#5] s (p92.effect s) := by
  have scalar : ScalarFrame [9#5] s (p92.effect s) := by
    constructor
    · exact p92.program s
    · simp (config := {decide := true, instances := true}) only
        [p92, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p92, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p92, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p96 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [0#5] s (p96.effect s) := by
  have scalar : ScalarFrame [0#5] s (p96.effect s) := by
    constructor
    · exact p96.program s
    · simp (config := {decide := true, instances := true}) only
        [p96, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p96, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p96, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p100 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [1#5] s (p100.effect s) := by
  have scalar : ScalarFrame [1#5] s (p100.effect s) := by
    constructor
    · exact p100.program s
    · simp (config := {decide := true, instances := true}) only
        [p100, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p100, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p100, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p104 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [2#5] s (p104.effect s) := by
  have scalar : ScalarFrame [2#5] s (p104.effect s) := by
    constructor
    · exact p104.program s
    · simp (config := {decide := true, instances := true}) only
        [p104, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p104, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p104, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p108 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [30#5] s (p108.effect s) := by
  have scalar : ScalarFrame [30#5] s (p108.effect s) := by
    constructor
    · exact p108.program s
    · simp (config := {decide := true, instances := true}) only
        [p108, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p108, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p108, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p112 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [0#5] s (p112.effect s) := by
  have scalar : ScalarFrame [0#5] s (p112.effect s) := by
    constructor
    · exact p112.program s
    · simp (config := {decide := true, instances := true}) only
        [p112, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p112, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p112, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p116 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [1#5] s (p116.effect s) := by
  have scalar : ScalarFrame [1#5] s (p116.effect s) := by
    constructor
    · exact p116.program s
    · simp (config := {decide := true, instances := true}) only
        [p116, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p116, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p116, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p120 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [30#5] s (p120.effect s) := by
  have scalar : ScalarFrame [30#5] s (p120.effect s) := by
    constructor
    · exact p120.program s
    · simp (config := {decide := true, instances := true}) only
        [p120, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p120, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p120, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p124 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [0#5] s (p124.effect s) := by
  have scalar : ScalarFrame [0#5] s (p124.effect s) := by
    constructor
    · exact p124.program s
    · simp (config := {decide := true, instances := true}) only
        [p124, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p124, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p124, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p128 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [31#5] s (p128.effect s) := by
  exact scalar_p28 s aligned

theorem scalar_p132 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p132.effect s) := by
  have scalar : ScalarFrame [] s (p132.effect s) := by
    constructor
    · exact p132.program s
    · simp (config := {decide := true, instances := true}) only
        [p132, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p132, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p132, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p136 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p136.effect s) := by
  have scalar : ScalarFrame [] s (p136.effect s) := by
    constructor
    · exact p136.program s
    · simp (config := {decide := true, instances := true}) only
        [p136, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p136, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p136, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p140 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [9#5] s (p140.effect s) := by
  have scalar : ScalarFrame [9#5] s (p140.effect s) := by
    constructor
    · exact p140.program s
    · simp (config := {decide := true, instances := true}) only
        [p140, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p140, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p140, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

end SszArm.Hash.Finalize

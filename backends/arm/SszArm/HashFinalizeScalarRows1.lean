import SszArm.HashFinalizeScalarRows0

namespace SszArm.Hash.Finalize

theorem scalar_p144 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [9#5] s (p144.effect s) := by
  have scalar : ScalarFrame [9#5] s (p144.effect s) := by
    constructor
    · exact p144.program s
    · simp (config := {decide := true, instances := true}) only
        [p144, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p144, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p144, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p148 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [10#5] s (p148.effect s) := by
  have scalar : ScalarFrame [10#5] s (p148.effect s) := by
    constructor
    · exact p148.program s
    · simp (config := {decide := true, instances := true}) only
        [p148, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p148, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p148, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p152 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p152.effect s) := by
  have scalar : ScalarFrame [] s (p152.effect s) := by
    constructor
    · exact p152.program s
    · simp (config := {decide := true, instances := true}) only
        [p152, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p152, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p152, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p156 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [10#5] s (p156.effect s) := by
  have scalar : ScalarFrame [10#5] s (p156.effect s) := by
    constructor
    · exact p156.program s
    · simp (config := {decide := true, instances := true}) only
        [p156, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p156, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p156, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p160 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [9#5] s (p160.effect s) := by
  have scalar : ScalarFrame [9#5] s (p160.effect s) := by
    constructor
    · exact p160.program s
    · simp (config := {decide := true, instances := true}) only
        [p160, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p160, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p160, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p164 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [31#5] s (p164.effect s) := by
  exact scalar_p52 s aligned

theorem scalar_p168 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [8#5] s (p168.effect s) := by
  have scalar : ScalarFrame [8#5] s (p168.effect s) := by
    constructor
    · exact p168.program s
    · simp (config := {decide := true, instances := true}) only
        [p168, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p168, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p168, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p172 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [1#5] s (p172.effect s) := by
  exact scalar_p100 s aligned

theorem scalar_p176 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [2#5] s (p176.effect s) := by
  have scalar : ScalarFrame [2#5] s (p176.effect s) := by
    constructor
    · exact p176.program s
    · simp (config := {decide := true, instances := true}) only
        [p176, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p176, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p176, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p180 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [0#5] s (p180.effect s) := by
  exact scalar_p96 s aligned

theorem scalar_p184 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [30#5] s (p184.effect s) := by
  have scalar : ScalarFrame [30#5] s (p184.effect s) := by
    constructor
    · exact p184.program s
    · simp (config := {decide := true, instances := true}) only
        [p184, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p184, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p184, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p188 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [8#5] s (p188.effect s) := by
  have scalar : ScalarFrame [8#5] s (p188.effect s) := by
    constructor
    · exact p188.program s
    · simp (config := {decide := true, instances := true}) only
        [p188, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p188, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p188, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p192 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [0#5] s (p192.effect s) := by
  exact scalar_p112 s aligned

theorem scalar_p196 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [1#5] s (p196.effect s) := by
  exact scalar_p116 s aligned

theorem scalar_p200 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [8#5] s (p200.effect s) := by
  have scalar : ScalarFrame [8#5] s (p200.effect s) := by
    constructor
    · exact p200.program s
    · simp (config := {decide := true, instances := true}) only
        [p200, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p200, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p200, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p204 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [8#5] s (p204.effect s) := by
  have scalar : ScalarFrame [8#5] s (p204.effect s) := by
    constructor
    · exact p204.program s
    · simp (config := {decide := true, instances := true}) only
        [p204, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p204, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p204, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p208 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p208.effect s) := by
  have scalar : ScalarFrame [] s (p208.effect s) := by
    constructor
    · exact p208.program s
    · simp (config := {decide := true, instances := true}) only
        [p208, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p208, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p208, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p212 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [30#5] s (p212.effect s) := by
  have scalar : ScalarFrame [30#5] s (p212.effect s) := by
    constructor
    · exact p212.program s
    · simp (config := {decide := true, instances := true}) only
        [p212, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p212, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p212, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p216 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [8#5, 9#5] s (p216.effect s) := by
  have scalar : ScalarFrame [8#5, 9#5] s (p216.effect s) := by
    constructor
    · exact p216.program s
    · simp (config := {decide := true, instances := true}) only
        [p216, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p216, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p216, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p220 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [10#5] s (p220.effect s) := by
  have scalar : ScalarFrame [10#5] s (p220.effect s) := by
    constructor
    · exact p220.program s
    · simp (config := {decide := true, instances := true}) only
        [p220, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p220, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p220, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p224 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [8#5] s (p224.effect s) := by
  have scalar : ScalarFrame [8#5] s (p224.effect s) := by
    constructor
    · exact p224.program s
    · simp (config := {decide := true, instances := true}) only
        [p224, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p224, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p224, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p228 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [9#5] s (p228.effect s) := by
  have scalar : ScalarFrame [9#5] s (p228.effect s) := by
    constructor
    · exact p228.program s
    · simp (config := {decide := true, instances := true}) only
        [p228, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p228, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p228, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p232 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p232.effect s) := by
  have scalar : ScalarFrame [] s (p232.effect s) := by
    constructor
    · exact p232.program s
    · simp (config := {decide := true, instances := true}) only
        [p232, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p232, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p232, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p236 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [11#5] s (p236.effect s) := by
  have scalar : ScalarFrame [11#5] s (p236.effect s) := by
    constructor
    · exact p236.program s
    · simp (config := {decide := true, instances := true}) only
        [p236, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p236, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p236, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p240 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [12#5] s (p240.effect s) := by
  have scalar : ScalarFrame [12#5] s (p240.effect s) := by
    constructor
    · exact p240.program s
    · simp (config := {decide := true, instances := true}) only
        [p240, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p240, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p240, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p244 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [8#5] s (p244.effect s) := by
  have scalar : ScalarFrame [8#5] s (p244.effect s) := by
    constructor
    · exact p244.program s
    · simp (config := {decide := true, instances := true}) only
        [p244, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p244, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p244, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p248 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [10#5] s (p248.effect s) := by
  have scalar : ScalarFrame [10#5] s (p248.effect s) := by
    constructor
    · exact p248.program s
    · simp (config := {decide := true, instances := true}) only
        [p248, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p248, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p248, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p252 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p252.effect s) := by
  exact scalar_p44 s aligned

theorem scalar_p256 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p256.effect s) := by
  have scalar : ScalarFrame [] s (p256.effect s) := by
    constructor
    · exact p256.program s
    · simp (config := {decide := true, instances := true}) only
        [p256, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p256, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p256, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p260 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [11#5] s (p260.effect s) := by
  have scalar : ScalarFrame [11#5] s (p260.effect s) := by
    constructor
    · exact p260.program s
    · simp (config := {decide := true, instances := true}) only
        [p260, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p260, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p260, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p264 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [13#5] s (p264.effect s) := by
  have scalar : ScalarFrame [13#5] s (p264.effect s) := by
    constructor
    · exact p264.program s
    · simp (config := {decide := true, instances := true}) only
        [p264, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p264, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p264, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p268 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p268.effect s) := by
  have scalar : ScalarFrame [] s (p268.effect s) := by
    constructor
    · exact p268.program s
    · simp (config := {decide := true, instances := true}) only
        [p268, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p268, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p268, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p272 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p272.effect s) := by
  have scalar : ScalarFrame [] s (p272.effect s) := by
    constructor
    · exact p272.program s
    · simp (config := {decide := true, instances := true}) only
        [p272, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p272, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p272, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p276 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [8#5] s (p276.effect s) := by
  have scalar : ScalarFrame [8#5] s (p276.effect s) := by
    constructor
    · exact p276.program s
    · simp (config := {decide := true, instances := true}) only
        [p276, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p276, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p276, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p280 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [9#5, 12#5] s (p280.effect s) := by
  have scalar : ScalarFrame [9#5, 12#5] s (p280.effect s) := by
    constructor
    · exact p280.program s
    · simp (config := {decide := true, instances := true}) only
        [p280, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p280, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p280, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p284 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p284.effect s) := by
  have scalar : ScalarFrame [] s (p284.effect s) := by
    constructor
    · exact p284.program s
    · simp (config := {decide := true, instances := true}) only
        [p284, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p284, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p284, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

end SszArm.Hash.Finalize

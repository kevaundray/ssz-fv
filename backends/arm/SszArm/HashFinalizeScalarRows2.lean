import SszArm.HashFinalizeScalarRows1

namespace SszArm.Hash.Finalize

theorem scalar_p288 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p288.effect s) := by
  have scalar : ScalarFrame [] s (p288.effect s) := by
    constructor
    · exact p288.program s
    · simp (config := {decide := true, instances := true}) only
        [p288, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p288, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p288, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p292 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [11#5] s (p292.effect s) := by
  have scalar : ScalarFrame [11#5] s (p292.effect s) := by
    constructor
    · exact p292.program s
    · simp (config := {decide := true, instances := true}) only
        [p292, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p292, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p292, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p296 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p296.effect s) := by
  have scalar : ScalarFrame [] s (p296.effect s) := by
    constructor
    · exact p296.program s
    · simp (config := {decide := true, instances := true}) only
        [p296, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p296, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p296, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p300 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [8#5] s (p300.effect s) := by
  have scalar : ScalarFrame [8#5] s (p300.effect s) := by
    constructor
    · exact p300.program s
    · simp (config := {decide := true, instances := true}) only
        [p300, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p300, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p300, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p304 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [10#5] s (p304.effect s) := by
  have scalar : ScalarFrame [10#5] s (p304.effect s) := by
    constructor
    · exact p304.program s
    · simp (config := {decide := true, instances := true}) only
        [p304, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p304, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p304, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p308 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [8#5] s (p308.effect s) := by
  have scalar : ScalarFrame [8#5] s (p308.effect s) := by
    constructor
    · exact p308.program s
    · simp (config := {decide := true, instances := true}) only
        [p308, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p308, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p308, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p312 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p312.effect s) := by
  have scalar : ScalarFrame [] s (p312.effect s) := by
    constructor
    · exact p312.program s
    · simp (config := {decide := true, instances := true}) only
        [p312, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p312, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p312, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p316 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [12#5] s (p316.effect s) := by
  have scalar : ScalarFrame [12#5] s (p316.effect s) := by
    constructor
    · exact p316.program s
    · simp (config := {decide := true, instances := true}) only
        [p316, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p316, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p316, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p320 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [9#5] s (p320.effect s) := by
  exact scalar_p228 s aligned

theorem scalar_p324 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p324.effect s) := by
  have scalar : ScalarFrame [] s (p324.effect s) := by
    constructor
    · exact p324.program s
    · simp (config := {decide := true, instances := true}) only
        [p324, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p324, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p324, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p328 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [10#5] s (p328.effect s) := by
  have scalar : ScalarFrame [10#5] s (p328.effect s) := by
    constructor
    · exact p328.program s
    · simp (config := {decide := true, instances := true}) only
        [p328, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p328, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p328, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p332 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p332.effect s) := by
  have scalar : ScalarFrame [] s (p332.effect s) := by
    constructor
    · exact p332.program s
    · simp (config := {decide := true, instances := true}) only
        [p332, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p332, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p332, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p336 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [8#5] s (p336.effect s) := by
  exact scalar_p300 s aligned

theorem scalar_p340 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [12#5] s (p340.effect s) := by
  have scalar : ScalarFrame [12#5] s (p340.effect s) := by
    constructor
    · exact p340.program s
    · simp (config := {decide := true, instances := true}) only
        [p340, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p340, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p340, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p344 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p344.effect s) := by
  have scalar : ScalarFrame [] s (p344.effect s) := by
    constructor
    · exact p344.program s
    · simp (config := {decide := true, instances := true}) only
        [p344, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p344, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p344, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p348 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [10#5] s (p348.effect s) := by
  have scalar : ScalarFrame [10#5] s (p348.effect s) := by
    constructor
    · exact p348.program s
    · simp (config := {decide := true, instances := true}) only
        [p348, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p348, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p348, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p352 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [8#5] s (p352.effect s) := by
  have scalar : ScalarFrame [8#5] s (p352.effect s) := by
    constructor
    · exact p352.program s
    · simp (config := {decide := true, instances := true}) only
        [p352, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p352, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p352, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p356 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p356.effect s) := by
  have scalar : ScalarFrame [] s (p356.effect s) := by
    constructor
    · exact p356.program s
    · simp (config := {decide := true, instances := true}) only
        [p356, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p356, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p356, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p360 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [9#5] s (p360.effect s) := by
  have scalar : ScalarFrame [9#5] s (p360.effect s) := by
    constructor
    · exact p360.program s
    · simp (config := {decide := true, instances := true}) only
        [p360, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p360, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p360, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p364 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p364.effect s) := by
  exact scalar_p324 s aligned

theorem scalar_p368 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [10#5, 11#5] s (p368.effect s) := by
  have scalar : ScalarFrame [10#5, 11#5] s (p368.effect s) := by
    constructor
    · exact p368.program s
    · simp (config := {decide := true, instances := true}) only
        [p368, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p368, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p368, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p372 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p372.effect s) := by
  have scalar : ScalarFrame [] s (p372.effect s) := by
    constructor
    · exact p372.program s
    · simp (config := {decide := true, instances := true}) only
        [p372, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p372, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p372, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p376 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p376.effect s) := by
  exact scalar_p332 s aligned

theorem scalar_p380 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [8#5] s (p380.effect s) := by
  exact scalar_p300 s aligned

theorem scalar_p384 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [11#5] s (p384.effect s) := by
  have scalar : ScalarFrame [11#5] s (p384.effect s) := by
    constructor
    · exact p384.program s
    · simp (config := {decide := true, instances := true}) only
        [p384, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p384, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p384, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p388 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [10#5] s (p388.effect s) := by
  have scalar : ScalarFrame [10#5] s (p388.effect s) := by
    constructor
    · exact p388.program s
    · simp (config := {decide := true, instances := true}) only
        [p388, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p388, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p388, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p392 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [9#5] s (p392.effect s) := by
  have scalar : ScalarFrame [9#5] s (p392.effect s) := by
    constructor
    · exact p392.program s
    · simp (config := {decide := true, instances := true}) only
        [p392, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p392, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p392, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p396 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [8#5] s (p396.effect s) := by
  have scalar : ScalarFrame [8#5] s (p396.effect s) := by
    constructor
    · exact p396.program s
    · simp (config := {decide := true, instances := true}) only
        [p396, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p396, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p396, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p400 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p400.effect s) := by
  exact scalar_p312 s aligned

theorem scalar_p404 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [12#5] s (p404.effect s) := by
  exact scalar_p316 s aligned

theorem scalar_p408 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p408.effect s) := by
  have scalar : ScalarFrame [] s (p408.effect s) := by
    constructor
    · exact p408.program s
    · simp (config := {decide := true, instances := true}) only
        [p408, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p408, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p408, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p412 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [9#5] s (p412.effect s) := by
  have scalar : ScalarFrame [9#5] s (p412.effect s) := by
    constructor
    · exact p412.program s
    · simp (config := {decide := true, instances := true}) only
        [p412, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p412, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p412, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p416 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p416.effect s) := by
  exact scalar_p332 s aligned

theorem scalar_p420 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [8#5] s (p420.effect s) := by
  exact scalar_p300 s aligned

theorem scalar_p424 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [12#5] s (p424.effect s) := by
  have scalar : ScalarFrame [12#5] s (p424.effect s) := by
    constructor
    · exact p424.program s
    · simp (config := {decide := true, instances := true}) only
        [p424, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p424, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p424, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

theorem scalar_p428 (s : ArmState) (aligned : CheckSPAlignment s) :
    ScalarStep [] s (p428.effect s) := by
  have scalar : ScalarFrame [] s (p428.effect s) := by
    constructor
    · exact p428.program s
    · simp (config := {decide := true, instances := true}) only
        [p428, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
    · intro reg different
      arm_word_nf at different
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at different
      simp (config := {decide := true, instances := true})
        (disch := first | assumption | decide) only
        [p428, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         NatExact.r_gpr_w, different, aligned]
    · intro reg
      simp (config := {decide := true, instances := true}) only
        [p428, Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, aligned]
  refine ⟨scalar, ?_⟩
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    scalar.registers 31#5 (by decide)] using aligned

end SszArm.Hash.Finalize

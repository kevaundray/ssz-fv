import SszArm.MeasureBitsAllocOps
import SszArm.DelimitedIntegerFacts

namespace SszArm.Measure.Bits.Alloc

theorem progressive_loadBase_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .progressive .loadBase).1) :
    stepi s = effect .progressive base .loadBase s := by
  have fetched := body_codeAt code (row .progressive .loadBase) (by
    simp only [bodyProgram, List.mem_append]; decide)
  simp only [row, Site.entry, Op.index, instructionWord] at fetched pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, put, next, commit, storeWords, Site.baseReg, Site.usedReg,
     Site.workReg, Site.tempReg, Site.pointerReg, Site.countReg, Site.lowReg,
     Site.highReg, Site.entry, Udivti3.compare, Udivti3.next, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
     BitVec.sub_eq_add_neg, aligned, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, Delimited.and_ones64, pc]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem progressive_loadUsed_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .progressive .loadUsed).1) :
    stepi s = effect .progressive base .loadUsed s := by
  have fetched := body_codeAt code (row .progressive .loadUsed) (by
    simp only [bodyProgram, List.mem_append]; decide)
  simp only [row, Site.entry, Op.index, instructionWord] at fetched pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, put, next, commit, storeWords, Site.baseReg, Site.usedReg,
     Site.workReg, Site.tempReg, Site.pointerReg, Site.countReg, Site.lowReg,
     Site.highReg, Site.entry, Udivti3.compare, Udivti3.next, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
     BitVec.sub_eq_add_neg, aligned, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, Delimited.and_ones64, pc]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem progressive_addAddress_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .progressive .addAddress).1) :
    stepi s = effect .progressive base .addAddress s := by
  have fetched := body_codeAt code (row .progressive .addAddress) (by
    simp only [bodyProgram, List.mem_append]; decide)
  simp only [row, Site.entry, Op.index, instructionWord] at fetched pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, put, next, commit, storeWords, Site.baseReg, Site.usedReg,
     Site.workReg, Site.tempReg, Site.pointerReg, Site.countReg, Site.lowReg,
     Site.highReg, Site.entry, Udivti3.compare, Udivti3.next, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
     BitVec.sub_eq_add_neg, aligned, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, Delimited.and_ones64, pc]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem progressive_addressGuard_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .progressive .addressGuard).1) :
    stepi s = effect .progressive base .addressGuard s := by
  have fetched := body_codeAt code (row .progressive .addressGuard) (by
    simp only [bodyProgram, List.mem_append]; decide)
  simp only [row, Site.entry, Op.index, instructionWord] at fetched pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, put, next, commit, storeWords, Site.baseReg, Site.usedReg,
     Site.workReg, Site.tempReg, Site.pointerReg, Site.countReg, Site.lowReg,
     Site.highReg, Site.entry, Udivti3.compare, Udivti3.next, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
     BitVec.sub_eq_add_neg, aligned, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, Delimited.and_ones64, pc]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem progressive_compareAlignment_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .progressive .compareAlignment).1) :
    stepi s = effect .progressive base .compareAlignment s := by
  have fetched := body_codeAt code (row .progressive .compareAlignment) (by
    simp only [bodyProgram, List.mem_append]; decide)
  simp only [row, Site.entry, Op.index, instructionWord] at fetched pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, put, next, commit, storeWords, Site.baseReg, Site.usedReg,
     Site.workReg, Site.tempReg, Site.pointerReg, Site.countReg, Site.lowReg,
     Site.highReg, Site.entry, Udivti3.compare, Udivti3.next, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
     BitVec.sub_eq_add_neg, aligned, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, Delimited.and_ones64, pc]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem progressive_alignmentGuard_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .progressive .alignmentGuard).1) :
    stepi s = effect .progressive base .alignmentGuard s := by
  have fetched := body_codeAt code (row .progressive .alignmentGuard) (by
    simp only [bodyProgram, List.mem_append]; decide)
  simp only [row, Site.entry, Op.index, instructionWord] at fetched pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, put, next, commit, storeWords, Site.baseReg, Site.usedReg,
     Site.workReg, Site.tempReg, Site.pointerReg, Site.countReg, Site.lowReg,
     Site.highReg, Site.entry, Udivti3.compare, Udivti3.next, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
     BitVec.sub_eq_add_neg, aligned, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, Delimited.and_ones64, pc]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem progressive_addPadding_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .progressive .addPadding).1) :
    stepi s = effect .progressive base .addPadding s := by
  have fetched := body_codeAt code (row .progressive .addPadding) (by
    simp only [bodyProgram, List.mem_append]; decide)
  simp only [row, Site.entry, Op.index, instructionWord] at fetched pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, put, next, commit, storeWords, Site.baseReg, Site.usedReg,
     Site.workReg, Site.tempReg, Site.pointerReg, Site.countReg, Site.lowReg,
     Site.highReg, Site.entry, Udivti3.compare, Udivti3.next, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
     BitVec.sub_eq_add_neg, aligned, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, Delimited.and_ones64, pc]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem progressive_maskPadding_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .progressive .maskPadding).1) :
    stepi s = effect .progressive base .maskPadding s := by
  have fetched := body_codeAt code (row .progressive .maskPadding) (by
    simp only [bodyProgram, List.mem_append]; decide)
  simp only [row, Site.entry, Op.index, instructionWord] at fetched pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, put, next, commit, storeWords, Site.baseReg, Site.usedReg,
     Site.workReg, Site.tempReg, Site.pointerReg, Site.countReg, Site.lowReg,
     Site.highReg, Site.entry, Udivti3.compare, Udivti3.next, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
     BitVec.sub_eq_add_neg, aligned, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, Delimited.and_ones64, pc]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem progressive_subtractAddress_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .progressive .subtractAddress).1) :
    stepi s = effect .progressive base .subtractAddress s := by
  have fetched := body_codeAt code (row .progressive .subtractAddress) (by
    simp only [bodyProgram, List.mem_append]; decide)
  simp only [row, Site.entry, Op.index, instructionWord] at fetched pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, put, next, commit, storeWords, Site.baseReg, Site.usedReg,
     Site.workReg, Site.tempReg, Site.pointerReg, Site.countReg, Site.lowReg,
     Site.highReg, Site.entry, Udivti3.compare, Udivti3.next, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
     BitVec.sub_eq_add_neg, aligned, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, Delimited.and_ones64, pc]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem progressive_addUsed_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .progressive .addUsed).1) :
    stepi s = effect .progressive base .addUsed s := by
  have fetched := body_codeAt code (row .progressive .addUsed) (by
    simp only [bodyProgram, List.mem_append]; decide)
  simp only [row, Site.entry, Op.index, instructionWord] at fetched pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, put, next, commit, storeWords, Site.baseReg, Site.usedReg,
     Site.workReg, Site.tempReg, Site.pointerReg, Site.countReg, Site.lowReg,
     Site.highReg, Site.entry, Udivti3.compare, Udivti3.next, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
     BitVec.sub_eq_add_neg, aligned, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, Delimited.and_ones64, pc]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem progressive_usedGuard_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .progressive .usedGuard).1) :
    stepi s = effect .progressive base .usedGuard s := by
  have fetched := body_codeAt code (row .progressive .usedGuard) (by
    simp only [bodyProgram, List.mem_append]; decide)
  simp only [row, Site.entry, Op.index, instructionWord] at fetched pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, put, next, commit, storeWords, Site.baseReg, Site.usedReg,
     Site.workReg, Site.tempReg, Site.pointerReg, Site.countReg, Site.lowReg,
     Site.highReg, Site.entry, Udivti3.compare, Udivti3.next, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
     BitVec.sub_eq_add_neg, aligned, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, Delimited.and_ones64, pc]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem progressive_compareSize_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .progressive .compareSize).1) :
    stepi s = effect .progressive base .compareSize s := by
  have fetched := body_codeAt code (row .progressive .compareSize) (by
    simp only [bodyProgram, List.mem_append]; decide)
  simp only [row, Site.entry, Op.index, instructionWord] at fetched pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, put, next, commit, storeWords, Site.baseReg, Site.usedReg,
     Site.workReg, Site.tempReg, Site.pointerReg, Site.countReg, Site.lowReg,
     Site.highReg, Site.entry, Udivti3.compare, Udivti3.next, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
     BitVec.sub_eq_add_neg, aligned, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, Delimited.and_ones64, pc]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem progressive_sizeGuard_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .progressive .sizeGuard).1) :
    stepi s = effect .progressive base .sizeGuard s := by
  have fetched := body_codeAt code (row .progressive .sizeGuard) (by
    simp only [bodyProgram, List.mem_append]; decide)
  simp only [row, Site.entry, Op.index, instructionWord] at fetched pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, put, next, commit, storeWords, Site.baseReg, Site.usedReg,
     Site.workReg, Site.tempReg, Site.pointerReg, Site.countReg, Site.lowReg,
     Site.highReg, Site.entry, Udivti3.compare, Udivti3.next, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
     BitVec.sub_eq_add_neg, aligned, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, Delimited.and_ones64, pc]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem progressive_loadCapacity_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .progressive .loadCapacity).1) :
    stepi s = effect .progressive base .loadCapacity s := by
  have fetched := body_codeAt code (row .progressive .loadCapacity) (by
    simp only [bodyProgram, List.mem_append]; decide)
  simp only [row, Site.entry, Op.index, instructionWord] at fetched pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, put, next, commit, storeWords, Site.baseReg, Site.usedReg,
     Site.workReg, Site.tempReg, Site.pointerReg, Site.countReg, Site.lowReg,
     Site.highReg, Site.entry, Udivti3.compare, Udivti3.next, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
     BitVec.sub_eq_add_neg, aligned, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, Delimited.and_ones64, pc]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem progressive_addSize_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .progressive .addSize).1) :
    stepi s = effect .progressive base .addSize s := by
  have fetched := body_codeAt code (row .progressive .addSize) (by
    simp only [bodyProgram, List.mem_append]; decide)
  simp only [row, Site.entry, Op.index, instructionWord] at fetched pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, put, next, commit, storeWords, Site.baseReg, Site.usedReg,
     Site.workReg, Site.tempReg, Site.pointerReg, Site.countReg, Site.lowReg,
     Site.highReg, Site.entry, Udivti3.compare, Udivti3.next, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
     BitVec.sub_eq_add_neg, aligned, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, Delimited.and_ones64, pc]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem progressive_compareCapacity_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .progressive .compareCapacity).1) :
    stepi s = effect .progressive base .compareCapacity s := by
  have fetched := body_codeAt code (row .progressive .compareCapacity) (by
    simp only [bodyProgram, List.mem_append]; decide)
  simp only [row, Site.entry, Op.index, instructionWord] at fetched pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, put, next, commit, storeWords, Site.baseReg, Site.usedReg,
     Site.workReg, Site.tempReg, Site.pointerReg, Site.countReg, Site.lowReg,
     Site.highReg, Site.entry, Udivti3.compare, Udivti3.next, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
     BitVec.sub_eq_add_neg, aligned, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, Delimited.and_ones64, pc]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem progressive_capacityGuard_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .progressive .capacityGuard).1) :
    stepi s = effect .progressive base .capacityGuard s := by
  have fetched := body_codeAt code (row .progressive .capacityGuard) (by
    simp only [bodyProgram, List.mem_append]; decide)
  simp only [row, Site.entry, Op.index, instructionWord] at fetched pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, put, next, commit, storeWords, Site.baseReg, Site.usedReg,
     Site.workReg, Site.tempReg, Site.pointerReg, Site.countReg, Site.lowReg,
     Site.highReg, Site.entry, Udivti3.compare, Udivti3.next, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
     BitVec.sub_eq_add_neg, aligned, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, Delimited.and_ones64, pc]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem progressive_addPointer_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .progressive .addPointer).1) :
    stepi s = effect .progressive base .addPointer s := by
  have fetched := body_codeAt code (row .progressive .addPointer) (by
    simp only [bodyProgram, List.mem_append]; decide)
  simp only [row, Site.entry, Op.index, instructionWord] at fetched pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, put, next, commit, storeWords, Site.baseReg, Site.usedReg,
     Site.workReg, Site.tempReg, Site.pointerReg, Site.countReg, Site.lowReg,
     Site.highReg, Site.entry, Udivti3.compare, Udivti3.next, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
     BitVec.sub_eq_add_neg, aligned, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, Delimited.and_ones64, pc]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem progressive_finish0_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .progressive .finish0).1) :
    stepi s = effect .progressive base .finish0 s := by
  have fetched := body_codeAt code (row .progressive .finish0) (by
    simp only [bodyProgram, List.mem_append]; decide)
  simp only [row, Site.entry, Op.index, instructionWord] at fetched pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, put, next, commit, storeWords, Site.baseReg, Site.usedReg,
     Site.workReg, Site.tempReg, Site.pointerReg, Site.countReg, Site.lowReg,
     Site.highReg, Site.entry, Udivti3.compare, Udivti3.next, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
     BitVec.sub_eq_add_neg, aligned, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, Delimited.and_ones64, pc]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem progressive_finish1_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .progressive .finish1).1) :
    stepi s = effect .progressive base .finish1 s := by
  have fetched := body_codeAt code (row .progressive .finish1) (by
    simp only [bodyProgram, List.mem_append]; decide)
  simp only [row, Site.entry, Op.index, instructionWord] at fetched pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, put, next, commit, storeWords, Site.baseReg, Site.usedReg,
     Site.workReg, Site.tempReg, Site.pointerReg, Site.countReg, Site.lowReg,
     Site.highReg, Site.entry, Udivti3.compare, Udivti3.next, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
     BitVec.sub_eq_add_neg, aligned, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, Delimited.and_ones64, pc]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem progressive_finish2_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .progressive .finish2).1) :
    stepi s = effect .progressive base .finish2 s := by
  have fetched := body_codeAt code (row .progressive .finish2) (by
    simp only [bodyProgram, List.mem_append]; decide)
  simp only [row, Site.entry, Op.index, instructionWord] at fetched pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
    (fetch_inst_from_program.trans fetched) rfl]
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [effect, put, next, commit, storeWords, Site.baseReg, Site.usedReg,
     Site.workReg, Site.tempReg, Site.pointerReg, Site.countReg, Site.lowReg,
     Site.highReg, Site.entry, Udivti3.compare, Udivti3.next, exec_inst,
     state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
     BitVec.sub_eq_add_neg, aligned, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, Delimited.and_ones64, pc]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

end SszArm.Measure.Bits.Alloc

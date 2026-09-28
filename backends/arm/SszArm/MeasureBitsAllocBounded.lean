import SszArm.MeasureBitsAllocOps
import SszArm.DelimitedIntegerFacts

namespace SszArm.Measure.Bits.Alloc

theorem bounded_loadBase_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .bounded .loadBase).1) :
    stepi s = effect .bounded base .loadBase s := by
  have fetched := body_codeAt code (row .bounded .loadBase) (by
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

theorem bounded_loadUsed_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .bounded .loadUsed).1) :
    stepi s = effect .bounded base .loadUsed s := by
  have fetched := body_codeAt code (row .bounded .loadUsed) (by
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

theorem bounded_addAddress_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .bounded .addAddress).1) :
    stepi s = effect .bounded base .addAddress s := by
  have fetched := body_codeAt code (row .bounded .addAddress) (by
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

theorem bounded_addressGuard_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .bounded .addressGuard).1) :
    stepi s = effect .bounded base .addressGuard s := by
  have fetched := body_codeAt code (row .bounded .addressGuard) (by
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

theorem bounded_compareAlignment_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .bounded .compareAlignment).1) :
    stepi s = effect .bounded base .compareAlignment s := by
  have fetched := body_codeAt code (row .bounded .compareAlignment) (by
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

theorem bounded_alignmentGuard_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .bounded .alignmentGuard).1) :
    stepi s = effect .bounded base .alignmentGuard s := by
  have fetched := body_codeAt code (row .bounded .alignmentGuard) (by
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

theorem bounded_addPadding_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .bounded .addPadding).1) :
    stepi s = effect .bounded base .addPadding s := by
  have fetched := body_codeAt code (row .bounded .addPadding) (by
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

theorem bounded_maskPadding_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .bounded .maskPadding).1) :
    stepi s = effect .bounded base .maskPadding s := by
  have fetched := body_codeAt code (row .bounded .maskPadding) (by
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

theorem bounded_subtractAddress_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .bounded .subtractAddress).1) :
    stepi s = effect .bounded base .subtractAddress s := by
  have fetched := body_codeAt code (row .bounded .subtractAddress) (by
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

theorem bounded_addUsed_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .bounded .addUsed).1) :
    stepi s = effect .bounded base .addUsed s := by
  have fetched := body_codeAt code (row .bounded .addUsed) (by
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

theorem bounded_usedGuard_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .bounded .usedGuard).1) :
    stepi s = effect .bounded base .usedGuard s := by
  have fetched := body_codeAt code (row .bounded .usedGuard) (by
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

theorem bounded_compareSize_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .bounded .compareSize).1) :
    stepi s = effect .bounded base .compareSize s := by
  have fetched := body_codeAt code (row .bounded .compareSize) (by
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

theorem bounded_sizeGuard_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .bounded .sizeGuard).1) :
    stepi s = effect .bounded base .sizeGuard s := by
  have fetched := body_codeAt code (row .bounded .sizeGuard) (by
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

theorem bounded_loadCapacity_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .bounded .loadCapacity).1) :
    stepi s = effect .bounded base .loadCapacity s := by
  have fetched := body_codeAt code (row .bounded .loadCapacity) (by
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

theorem bounded_addSize_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .bounded .addSize).1) :
    stepi s = effect .bounded base .addSize s := by
  have fetched := body_codeAt code (row .bounded .addSize) (by
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

theorem bounded_compareCapacity_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .bounded .compareCapacity).1) :
    stepi s = effect .bounded base .compareCapacity s := by
  have fetched := body_codeAt code (row .bounded .compareCapacity) (by
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

theorem bounded_capacityGuard_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .bounded .capacityGuard).1) :
    stepi s = effect .bounded base .capacityGuard s := by
  have fetched := body_codeAt code (row .bounded .capacityGuard) (by
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

theorem bounded_addPointer_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .bounded .addPointer).1) :
    stepi s = effect .bounded base .addPointer s := by
  have fetched := body_codeAt code (row .bounded .addPointer) (by
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

theorem bounded_finish0_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .bounded .finish0).1) :
    stepi s = effect .bounded base .finish0 s := by
  have fetched := body_codeAt code (row .bounded .finish0) (by
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

theorem bounded_finish1_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .bounded .finish1).1) :
    stepi s = effect .bounded base .finish1 s := by
  have fetched := body_codeAt code (row .bounded .finish1) (by
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

theorem bounded_finish2_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .bounded .finish2).1) :
    stepi s = effect .bounded base .finish2 s := by
  have fetched := body_codeAt code (row .bounded .finish2) (by
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

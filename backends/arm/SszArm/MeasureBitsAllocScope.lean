import SszArm.MeasureBitsAllocOps
import SszArm.DelimitedIntegerFacts

namespace SszArm.Measure.Bits.Alloc

theorem scope_loadBase_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .scope .loadBase).1) :
    stepi s = effect .scope base .loadBase s := by
  have fetched := body_codeAt code (row .scope .loadBase) (by
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

theorem scope_loadUsed_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .scope .loadUsed).1) :
    stepi s = effect .scope base .loadUsed s := by
  have fetched := body_codeAt code (row .scope .loadUsed) (by
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

theorem scope_addAddress_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .scope .addAddress).1) :
    stepi s = effect .scope base .addAddress s := by
  have fetched := body_codeAt code (row .scope .addAddress) (by
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

theorem scope_addressGuard_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .scope .addressGuard).1) :
    stepi s = effect .scope base .addressGuard s := by
  have fetched := body_codeAt code (row .scope .addressGuard) (by
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

theorem scope_compareAlignment_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .scope .compareAlignment).1) :
    stepi s = effect .scope base .compareAlignment s := by
  have fetched := body_codeAt code (row .scope .compareAlignment) (by
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

theorem scope_alignmentGuard_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .scope .alignmentGuard).1) :
    stepi s = effect .scope base .alignmentGuard s := by
  have fetched := body_codeAt code (row .scope .alignmentGuard) (by
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

theorem scope_addPadding_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .scope .addPadding).1) :
    stepi s = effect .scope base .addPadding s := by
  have fetched := body_codeAt code (row .scope .addPadding) (by
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

theorem scope_maskPadding_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .scope .maskPadding).1) :
    stepi s = effect .scope base .maskPadding s := by
  have fetched := body_codeAt code (row .scope .maskPadding) (by
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

theorem scope_subtractAddress_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .scope .subtractAddress).1) :
    stepi s = effect .scope base .subtractAddress s := by
  have fetched := body_codeAt code (row .scope .subtractAddress) (by
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

theorem scope_addUsed_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .scope .addUsed).1) :
    stepi s = effect .scope base .addUsed s := by
  have fetched := body_codeAt code (row .scope .addUsed) (by
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

theorem scope_usedGuard_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .scope .usedGuard).1) :
    stepi s = effect .scope base .usedGuard s := by
  have fetched := body_codeAt code (row .scope .usedGuard) (by
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

theorem scope_compareSize_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .scope .compareSize).1) :
    stepi s = effect .scope base .compareSize s := by
  have fetched := body_codeAt code (row .scope .compareSize) (by
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

theorem scope_sizeGuard_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .scope .sizeGuard).1) :
    stepi s = effect .scope base .sizeGuard s := by
  have fetched := body_codeAt code (row .scope .sizeGuard) (by
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

theorem scope_loadCapacity_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .scope .loadCapacity).1) :
    stepi s = effect .scope base .loadCapacity s := by
  have fetched := body_codeAt code (row .scope .loadCapacity) (by
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

theorem scope_addSize_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .scope .addSize).1) :
    stepi s = effect .scope base .addSize s := by
  have fetched := body_codeAt code (row .scope .addSize) (by
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

theorem scope_compareCapacity_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .scope .compareCapacity).1) :
    stepi s = effect .scope base .compareCapacity s := by
  have fetched := body_codeAt code (row .scope .compareCapacity) (by
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

theorem scope_capacityGuard_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .scope .capacityGuard).1) :
    stepi s = effect .scope base .capacityGuard s := by
  have fetched := body_codeAt code (row .scope .capacityGuard) (by
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

theorem scope_addPointer_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .scope .addPointer).1) :
    stepi s = effect .scope base .addPointer s := by
  have fetched := body_codeAt code (row .scope .addPointer) (by
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

theorem scope_finish0_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .scope .finish0).1) :
    stepi s = effect .scope base .finish0 s := by
  have fetched := body_codeAt code (row .scope .finish0) (by
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

theorem scope_finish1_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .scope .finish1).1) :
    stepi s = effect .scope base .finish1 s := by
  have fetched := body_codeAt code (row .scope .finish1) (by
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

theorem scope_finish2_step (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (row .scope .finish2).1) :
    stepi s = effect .scope base .finish2 s := by
  have fetched := body_codeAt code (row .scope .finish2) (by
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

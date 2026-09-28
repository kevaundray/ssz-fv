import SszArm.SerializeOps

namespace SszArm.Serialize

open UintCodec

private theorem word_p0 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xd10243ff#32) :
    stepi s = Op.p0.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p4 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xa9065ffe#32) :
    stepi s = Op.p4.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p8 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xa90757f6#32) :
    stepi s = Op.p8.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p12 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xa9084ff4#32) :
    stepi s = Op.p12.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p16 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xaa0403f7#32) :
    stepi s = Op.p16.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p20 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xaa0303f4#32) :
    stepi s = Op.p20.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p24 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xaa0003f3#32) :
    stepi s = Op.p24.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p28 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x910063e0#32) :
    stepi s = Op.p28.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p32 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xaa0503e3#32) :
    stepi s = Op.p32.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p36 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x52800024#32) :
    stepi s = Op.p36.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p40 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xaa0203f5#32) :
    stepi s = Op.p40.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p44 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xaa0103f6#32) :
    stepi s = Op.p44.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p48 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x97ffdabd#32)
    (pc : read_pc s = base + 48#64) :
    stepi s = Op.p48.effect base s := by
  change r .PC s = _ at pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, pc, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p52 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xa941b3eb#32) :
    stepi s = Op.p52.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p56 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xb9405be9#32) :
    stepi s = Op.p56.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p60 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xa94297e8#32) :
    stepi s = Op.p60.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p64 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xf9401fea#32) :
    stepi s = Op.p64.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p68 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xa900b3eb#32) :
    stepi s = Op.p68.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p72 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x34000209#32)
    (pc : read_pc s = base + 72#64) :
    stepi s = Op.p72.effect base s := by
  change r .PC s = _ at pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, pc, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p76 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xa94433eb#32) :
    stepi s = Op.p76.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p80 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xf9402bed#32) :
    stepi s = Op.p80.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p84 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xa9011668#32) :
    stepi s = Op.p84.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p88 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xb9405fe8#32) :
    stepi s = Op.p88.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p92 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xf9001e6d#32) :
    stepi s = Op.p92.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p96 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xa902b26b#32) :
    stepi s = Op.p96.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p100 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xa940b3eb#32) :
    stepi s = Op.p100.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p104 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xf900126a#32) :
    stepi s = Op.p104.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p108 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x29082269#32) :
    stepi s = Op.p108.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p112 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xa900326b#32) :
    stepi s = Op.p112.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p116 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xa9484ff4#32) :
    stepi s = Op.p116.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p120 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xa94757f6#32) :
    stepi s = Op.p120.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p124 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xa9465ffe#32) :
    stepi s = Op.p124.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p128 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x910243ff#32) :
    stepi s = Op.p128.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p132 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xd65f03c0#32) :
    stepi s = Op.p132.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p136 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xa940afe9#32) :
    stepi s = Op.p136.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p140 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xa90297e8#32) :
    stepi s = Op.p140.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p144 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xf9001fea#32) :
    stepi s = Op.p144.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p148 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xa901afe9#32) :
    stepi s = Op.p148.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p152 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xb4000888#32)
    (pc : read_pc s = base + 152#64) :
    stepi s = Op.p152.effect base s := by
  change r .PC s = _ at pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, pc, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p156 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xd10004aa#32) :
    stepi s = Op.p156.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p160 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xb100055f#32) :
    stepi s = Op.p160.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p164 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x540007e0#32)
    (pc : read_pc s = base + 164#64) :
    stepi s = Op.p164.effect base s := by
  change r .PC s = _ at pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, pc, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p168 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xd10043ff#32) :
    stepi s = Op.p168.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p172 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xf90003e9#32) :
    stepi s = Op.p172.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p176 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xaa0a03e9#32) :
    stepi s = Op.p176.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p180 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xd37df129#32) :
    stepi s = Op.p180.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p184 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x8b090109#32) :
    stepi s = Op.p184.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p188 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xf940012b#32) :
    stepi s = Op.p188.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p192 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xf94003e9#32) :
    stepi s = Op.p192.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p196 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x910043ff#32) :
    stepi s = Op.p196.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p204 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xd100054a#32) :
    stepi s = Op.p204.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p208 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xb4fffe8b#32)
    (pc : read_pc s = base + 208#64) :
    stepi s = Op.p208.effect base s := by
  change r .PC s = _ at pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, pc, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p212 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x91000529#32) :
    stepi s = Op.p212.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p216 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xf100053f#32) :
    stepi s = Op.p216.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p220 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x54000640#32)
    (pc : read_pc s = base + 220#64) :
    stepi s = Op.p220.effect base s := by
  change r .PC s = _ at pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, pc, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p224 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x52800028#32) :
    stepi s = Op.p224.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p236 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xf90007ea#32) :
    stepi s = Op.p236.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p240 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x91000269#32) :
    stepi s = Op.p240.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p244 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x9100c129#32) :
    stepi s = Op.p244.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p248 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xd280000a#32) :
    stepi s = Op.p248.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p252 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xf900012a#32) :
    stepi s = Op.p252.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p260 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xf900052a#32) :
    stepi s = Op.p260.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p264 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xf94007ea#32) :
    stepi s = Op.p264.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p292 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x91008129#32) :
    stepi s = Op.p292.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p340 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x91004129#32) :
    stepi s = Op.p340.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p388 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xf9000128#32) :
    stepi s = Op.p388.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p412 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x14000034#32)
    (pc : read_pc s = base + 412#64) :
    stepi s = Op.p412.effect base s := by
  change r .PC s = _ at pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, pc, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p416 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xb4000745#32)
    (pc : read_pc s = base + 416#64) :
    stepi s = Op.p416.effect base s := by
  change r .PC s = _ at pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, pc, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p420 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xf9400105#32) :
    stepi s = Op.p420.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p424 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xeb0502ff#32) :
    stepi s = Op.p424.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p428 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x540006e2#32)
    (pc : read_pc s = base + 428#64) :
    stepi s = Op.p428.effect base s := by
  change r .PC s = _ at pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, pc, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p620 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x52900028#32) :
    stepi s = Op.p620.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p624 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xb9004268#32) :
    stepi s = Op.p624.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p648 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x910063e3#32) :
    stepi s = Op.p648.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p652 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xaa1303e0#32) :
    stepi s = Op.p652.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p656 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xaa1603e1#32) :
    stepi s = Op.p656.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p660 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xaa1503e2#32) :
    stepi s = Op.p660.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p664 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0xaa1403e4#32) :
    stepi s = Op.p664.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

private theorem word_p668 (s : ArmState) (base : BitVec 64)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (fetched : s.program.find? (read_pc s) = some 0x97ffde62#32)
    (pc : read_pc s = base + 668#64) :
    stepi s = Op.p668.effect base s := by
  change r .PC s = _ at pc
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error rfl
    (fetch_inst_from_program.trans fetched) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Emit.Dispatch.next, Emit.Dispatch.compare64,
     measureOffset, emitOffset, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, aligned, pc, BitVec.add_assoc,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, uint_lsl3_mask, uint_and_ones, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The original word at each wrapper PC executes its explicit instruction effect. -/
theorem step (s : ArmState) (base : BitVec 64) (op : Op)
    (code : CodeAt s base) (pc : read_pc s = base + BitVec.ofNat 64 op.row.1)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) :
    stepi s = op.effect base s := by
  have image := body_codeAt code op.row (by cases op <;> decide)
  have fetched : s.program.find? (read_pc s) = some op.row.2 := by
    rw [pc]
    exact image
  cases op with
  | p0 => exact word_p0 s base error aligned fetched
  | p4 => exact word_p4 s base error aligned fetched
  | p8 => exact word_p8 s base error aligned fetched
  | p12 => exact word_p12 s base error aligned fetched
  | p16 => exact word_p16 s base error aligned fetched
  | p20 => exact word_p20 s base error aligned fetched
  | p24 => exact word_p24 s base error aligned fetched
  | p28 => exact word_p28 s base error aligned fetched
  | p32 => exact word_p32 s base error aligned fetched
  | p36 => exact word_p36 s base error aligned fetched
  | p40 => exact word_p40 s base error aligned fetched
  | p44 => exact word_p44 s base error aligned fetched
  | p48 => exact word_p48 s base error aligned fetched pc
  | p52 => exact word_p52 s base error aligned fetched
  | p56 => exact word_p56 s base error aligned fetched
  | p60 => exact word_p60 s base error aligned fetched
  | p64 => exact word_p64 s base error aligned fetched
  | p68 => exact word_p68 s base error aligned fetched
  | p72 => exact word_p72 s base error aligned fetched pc
  | p76 => exact word_p76 s base error aligned fetched
  | p80 => exact word_p80 s base error aligned fetched
  | p84 => exact word_p84 s base error aligned fetched
  | p88 => exact word_p88 s base error aligned fetched
  | p92 => exact word_p92 s base error aligned fetched
  | p96 => exact word_p96 s base error aligned fetched
  | p100 => exact word_p100 s base error aligned fetched
  | p104 => exact word_p104 s base error aligned fetched
  | p108 => exact word_p108 s base error aligned fetched
  | p112 => exact word_p112 s base error aligned fetched
  | p116 => exact word_p116 s base error aligned fetched
  | p120 => exact word_p120 s base error aligned fetched
  | p124 => exact word_p124 s base error aligned fetched
  | p128 => exact word_p128 s base error aligned fetched
  | p132 => exact word_p132 s base error aligned fetched
  | p136 => exact word_p136 s base error aligned fetched
  | p140 => exact word_p140 s base error aligned fetched
  | p144 => exact word_p144 s base error aligned fetched
  | p148 => exact word_p148 s base error aligned fetched
  | p152 => exact word_p152 s base error aligned fetched pc
  | p156 => exact word_p156 s base error aligned fetched
  | p160 => exact word_p160 s base error aligned fetched
  | p164 => exact word_p164 s base error aligned fetched pc
  | p168 => exact word_p168 s base error aligned fetched
  | p172 => exact word_p172 s base error aligned fetched
  | p176 => exact word_p176 s base error aligned fetched
  | p180 => exact word_p180 s base error aligned fetched
  | p184 => exact word_p184 s base error aligned fetched
  | p188 => exact word_p188 s base error aligned fetched
  | p192 => exact word_p192 s base error aligned fetched
  | p196 => exact word_p196 s base error aligned fetched
  | p200 => exact word_p176 s base error aligned fetched
  | p204 => exact word_p204 s base error aligned fetched
  | p208 => exact word_p208 s base error aligned fetched pc
  | p212 => exact word_p212 s base error aligned fetched
  | p216 => exact word_p216 s base error aligned fetched
  | p220 => exact word_p220 s base error aligned fetched pc
  | p224 => exact word_p224 s base error aligned fetched
  | p228 => exact word_p168 s base error aligned fetched
  | p232 => exact word_p172 s base error aligned fetched
  | p236 => exact word_p236 s base error aligned fetched
  | p240 => exact word_p240 s base error aligned fetched
  | p244 => exact word_p244 s base error aligned fetched
  | p248 => exact word_p248 s base error aligned fetched
  | p252 => exact word_p252 s base error aligned fetched
  | p256 => exact word_p248 s base error aligned fetched
  | p260 => exact word_p260 s base error aligned fetched
  | p264 => exact word_p264 s base error aligned fetched
  | p268 => exact word_p192 s base error aligned fetched
  | p272 => exact word_p196 s base error aligned fetched
  | p276 => exact word_p168 s base error aligned fetched
  | p280 => exact word_p172 s base error aligned fetched
  | p284 => exact word_p236 s base error aligned fetched
  | p288 => exact word_p240 s base error aligned fetched
  | p292 => exact word_p292 s base error aligned fetched
  | p296 => exact word_p248 s base error aligned fetched
  | p300 => exact word_p252 s base error aligned fetched
  | p304 => exact word_p248 s base error aligned fetched
  | p308 => exact word_p260 s base error aligned fetched
  | p312 => exact word_p264 s base error aligned fetched
  | p316 => exact word_p192 s base error aligned fetched
  | p320 => exact word_p196 s base error aligned fetched
  | p324 => exact word_p168 s base error aligned fetched
  | p328 => exact word_p172 s base error aligned fetched
  | p332 => exact word_p236 s base error aligned fetched
  | p336 => exact word_p240 s base error aligned fetched
  | p340 => exact word_p340 s base error aligned fetched
  | p344 => exact word_p248 s base error aligned fetched
  | p348 => exact word_p252 s base error aligned fetched
  | p352 => exact word_p248 s base error aligned fetched
  | p356 => exact word_p260 s base error aligned fetched
  | p360 => exact word_p264 s base error aligned fetched
  | p364 => exact word_p192 s base error aligned fetched
  | p368 => exact word_p196 s base error aligned fetched
  | p372 => exact word_p168 s base error aligned fetched
  | p376 => exact word_p172 s base error aligned fetched
  | p380 => exact word_p236 s base error aligned fetched
  | p384 => exact word_p240 s base error aligned fetched
  | p388 => exact word_p388 s base error aligned fetched
  | p392 => exact word_p248 s base error aligned fetched
  | p396 => exact word_p260 s base error aligned fetched
  | p400 => exact word_p264 s base error aligned fetched
  | p404 => exact word_p192 s base error aligned fetched
  | p408 => exact word_p196 s base error aligned fetched
  | p412 => exact word_p412 s base error aligned fetched pc
  | p416 => exact word_p416 s base error aligned fetched pc
  | p420 => exact word_p420 s base error aligned fetched
  | p424 => exact word_p424 s base error aligned fetched
  | p428 => exact word_p428 s base error aligned fetched pc
  | p432 => exact word_p224 s base error aligned fetched
  | p436 => exact word_p168 s base error aligned fetched
  | p440 => exact word_p172 s base error aligned fetched
  | p444 => exact word_p236 s base error aligned fetched
  | p448 => exact word_p240 s base error aligned fetched
  | p452 => exact word_p340 s base error aligned fetched
  | p456 => exact word_p248 s base error aligned fetched
  | p460 => exact word_p252 s base error aligned fetched
  | p464 => exact word_p248 s base error aligned fetched
  | p468 => exact word_p260 s base error aligned fetched
  | p472 => exact word_p264 s base error aligned fetched
  | p476 => exact word_p192 s base error aligned fetched
  | p480 => exact word_p196 s base error aligned fetched
  | p484 => exact word_p168 s base error aligned fetched
  | p488 => exact word_p172 s base error aligned fetched
  | p492 => exact word_p236 s base error aligned fetched
  | p496 => exact word_p240 s base error aligned fetched
  | p500 => exact word_p388 s base error aligned fetched
  | p504 => exact word_p248 s base error aligned fetched
  | p508 => exact word_p260 s base error aligned fetched
  | p512 => exact word_p264 s base error aligned fetched
  | p516 => exact word_p192 s base error aligned fetched
  | p520 => exact word_p196 s base error aligned fetched
  | p524 => exact word_p168 s base error aligned fetched
  | p528 => exact word_p172 s base error aligned fetched
  | p532 => exact word_p236 s base error aligned fetched
  | p536 => exact word_p240 s base error aligned fetched
  | p540 => exact word_p292 s base error aligned fetched
  | p544 => exact word_p248 s base error aligned fetched
  | p548 => exact word_p252 s base error aligned fetched
  | p552 => exact word_p248 s base error aligned fetched
  | p556 => exact word_p260 s base error aligned fetched
  | p560 => exact word_p264 s base error aligned fetched
  | p564 => exact word_p192 s base error aligned fetched
  | p568 => exact word_p196 s base error aligned fetched
  | p572 => exact word_p168 s base error aligned fetched
  | p576 => exact word_p172 s base error aligned fetched
  | p580 => exact word_p236 s base error aligned fetched
  | p584 => exact word_p240 s base error aligned fetched
  | p588 => exact word_p244 s base error aligned fetched
  | p592 => exact word_p248 s base error aligned fetched
  | p596 => exact word_p252 s base error aligned fetched
  | p600 => exact word_p248 s base error aligned fetched
  | p604 => exact word_p260 s base error aligned fetched
  | p608 => exact word_p264 s base error aligned fetched
  | p612 => exact word_p192 s base error aligned fetched
  | p616 => exact word_p196 s base error aligned fetched
  | p620 => exact word_p620 s base error aligned fetched
  | p624 => exact word_p624 s base error aligned fetched
  | p628 => exact word_p116 s base error aligned fetched
  | p632 => exact word_p120 s base error aligned fetched
  | p636 => exact word_p124 s base error aligned fetched
  | p640 => exact word_p128 s base error aligned fetched
  | p644 => exact word_p132 s base error aligned fetched
  | p648 => exact word_p648 s base error aligned fetched
  | p652 => exact word_p652 s base error aligned fetched
  | p656 => exact word_p656 s base error aligned fetched
  | p660 => exact word_p660 s base error aligned fetched
  | p664 => exact word_p664 s base error aligned fetched
  | p668 => exact word_p668 s base error aligned fetched pc
  | p672 => exact word_p116 s base error aligned fetched
  | p676 => exact word_p120 s base error aligned fetched
  | p680 => exact word_p124 s base error aligned fetched
  | p684 => exact word_p128 s base error aligned fetched
  | p688 => exact word_p132 s base error aligned fetched

@[simp] theorem Op.program (op : Op) (base : BitVec 64) (s : ArmState) :
    (op.effect base s).program = s.program := by
  cases op <;> simp [Op.effect, put, next, Emit.Dispatch.next,
    Emit.Dispatch.compare64, state_simp_rules]

@[simp] theorem Op.error (op : Op) (base : BitVec 64) (s : ArmState) :
    read_err (op.effect base s) = read_err s := by
  cases op <;> simp [Op.effect, put, next, Emit.Dispatch.next,
    Emit.Dispatch.compare64, state_simp_rules]

private theorem aligned_sub144 (x : BitVec 64) (aligned : Aligned x 4) :
    Aligned (x - 144#64) 4 := by
  simp only [Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat] at *
  bv_omega

private theorem aligned_add144 (x : BitVec 64) (aligned : Aligned x 4) :
    Aligned (x + 144#64) 4 := by
  simp only [Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat] at *
  bv_omega

private theorem op_aligned_entry0 (op : Op) (base : BitVec 64) (s : ArmState)
    (upper : op.row.1 < 64) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (op.effect base s) := by
  cases op <;> simp (config := { decide := true }) only [Op.row] at upper
  all_goals
    simp [Op.effect, put, next, Emit.Dispatch.next,
      Emit.Dispatch.compare64, state_simp_rules, aligned]
  exact aligned_sub144 _ (BoolCodec.stack_aligned s aligned)

private theorem op_aligned_entry64 (op : Op) (base : BitVec 64) (s : ArmState)
    (lower : 64 ≤ op.row.1) (upper : op.row.1 < 128) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (op.effect base s) := by
  cases op <;> simp (config := { decide := true }) only [Op.row] at lower upper
  all_goals
    simp [Op.effect, put, next, Emit.Dispatch.next,
      Emit.Dispatch.compare64, state_simp_rules, aligned]

private theorem op_aligned_entry128 (op : Op) (base : BitVec 64) (s : ArmState)
    (lower : 128 ≤ op.row.1) (upper : op.row.1 < 192) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (op.effect base s) := by
  cases op <;> simp (config := { decide := true }) only [Op.row] at lower upper
  all_goals
    simp [Op.effect, put, next, Emit.Dispatch.next,
      Emit.Dispatch.compare64, state_simp_rules, aligned]
  · exact aligned_add144 _ (BoolCodec.stack_aligned s aligned)
  · exact BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s aligned)

private theorem op_aligned_entry192 (op : Op) (base : BitVec 64) (s : ArmState)
    (lower : 192 ≤ op.row.1) (upper : op.row.1 < 224) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (op.effect base s) := by
  cases op <;> simp (config := { decide := true }) only [Op.row] at lower upper
  all_goals
    simp [Op.effect, put, next, Emit.Dispatch.next,
      Emit.Dispatch.compare64, state_simp_rules, aligned]
  exact BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s aligned)

private theorem op_aligned_entry (op : Op) (base : BitVec 64) (s : ArmState)
    (upper : op.row.1 < 224) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (op.effect base s) := by
  by_cases first : op.row.1 < 64
  · exact op_aligned_entry0 op base s first aligned
  · by_cases second : op.row.1 < 128
    · exact op_aligned_entry64 op base s (by omega) second aligned
    · by_cases third : op.row.1 < 192
      · exact op_aligned_entry128 op base s (by omega) third aligned
      · exact op_aligned_entry192 op base s (by omega) upper aligned

private theorem op_aligned_host (op : Op) (base : BitVec 64) (s : ArmState)
    (lower : 224 ≤ op.row.1) (upper : op.row.1 < 432) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (op.effect base s) := by
  cases op <;> simp (config := { decide := true }) only [Op.row] at lower upper
  all_goals
    simp [Op.effect, put, next, Emit.Dispatch.next,
      Emit.Dispatch.compare64, state_simp_rules, aligned]
  all_goals first
    | exact BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s aligned)
    | exact BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s aligned)

private theorem op_aligned_output432 (op : Op) (base : BitVec 64) (s : ArmState)
    (lower : 432 ≤ op.row.1) (upper : op.row.1 < 496) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (op.effect base s) := by
  cases op <;> simp (config := { decide := true }) only [Op.row] at lower upper
  all_goals
    simp [Op.effect, put, next, Emit.Dispatch.next,
      Emit.Dispatch.compare64, state_simp_rules, aligned]
  · exact BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s aligned)
  · exact BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s aligned)
  · exact BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s aligned)

private theorem op_aligned_output496 (op : Op) (base : BitVec 64) (s : ArmState)
    (lower : 496 ≤ op.row.1) (upper : op.row.1 < 560) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (op.effect base s) := by
  cases op <;> simp (config := { decide := true }) only [Op.row] at lower upper
  all_goals
    simp [Op.effect, put, next, Emit.Dispatch.next,
      Emit.Dispatch.compare64, state_simp_rules, aligned]
  · exact BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s aligned)
  · exact BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s aligned)

private theorem op_aligned_output560 (op : Op) (base : BitVec 64) (s : ArmState)
    (lower : 560 ≤ op.row.1) (upper : op.row.1 < 624) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (op.effect base s) := by
  cases op <;> simp (config := { decide := true }) only [Op.row] at lower upper
  all_goals
    simp [Op.effect, put, next, Emit.Dispatch.next,
      Emit.Dispatch.compare64, state_simp_rules, aligned]
  · exact BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s aligned)
  · exact BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s aligned)
  · exact BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s aligned)

private theorem op_aligned_output624 (op : Op) (base : BitVec 64) (s : ArmState)
    (lower : 624 ≤ op.row.1) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (op.effect base s) := by
  cases op <;> simp (config := { decide := true }) only [Op.row] at lower
  all_goals
    simp [Op.effect, put, next, Emit.Dispatch.next,
      Emit.Dispatch.compare64, state_simp_rules, aligned]
  all_goals exact aligned_add144 _ (BoolCodec.stack_aligned s aligned)

private theorem op_aligned_output (op : Op) (base : BitVec 64) (s : ArmState)
    (lower : 432 ≤ op.row.1) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (op.effect base s) := by
  by_cases first : op.row.1 < 496
  · exact op_aligned_output432 op base s lower first aligned
  · by_cases second : op.row.1 < 560
    · exact op_aligned_output496 op base s (by omega) second aligned
    · by_cases third : op.row.1 < 624
      · exact op_aligned_output560 op base s (by omega) third aligned
      · exact op_aligned_output624 op base s (by omega) aligned

theorem Op.aligned (op : Op) (base : BitVec 64) (s : ArmState)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (op.effect base s) := by
  by_cases entry : op.row.1 < 224
  · exact op_aligned_entry op base s entry aligned
  · by_cases host : op.row.1 < 432
    · exact op_aligned_host op base s (by omega) host aligned
    · exact op_aligned_output op base s (by omega) aligned

@[simp] theorem Op.vector (op : Op) (base : BitVec 64) (s : ArmState)
    (reg : BitVec 5) : r (.SFP reg) (op.effect base s) = r (.SFP reg) s := by
  cases op <;> simp [Op.effect, put, next, Emit.Dispatch.next,
    Emit.Dispatch.compare64, state_simp_rules]

/-- A finite sequence of the original wrapper instruction effects. -/
def block (base : BitVec 64) (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect base t) s

/-- Only current local PC observations are needed to connect consecutive effects. -/
def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      Follows base ops (op.effect base s)

theorem block_run (base : BitVec 64) (ops : List Op) (s : ArmState)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (follows : Follows base ops s) : run ops.length s = block base ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = block base ops (op.effect base s)
    rw [run, step s base op code follows.1 error aligned]
    exact ih _ (code.congr (op.program base s))
      ((op.error base s).trans error) (op.aligned base s aligned) follows.2

@[simp] theorem block_program (base : BitVec 64) (ops : List Op) (s : ArmState) :
    (block base ops s).program = s.program := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.program base s)

@[simp] theorem block_error (base : BitVec 64) (ops : List Op) (s : ArmState) :
    read_err (block base ops s) = read_err s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.error base s)

theorem block_aligned (base : BitVec 64) (ops : List Op) (s : ArmState)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (block base ops s) := by
  induction ops generalizing s with
  | nil => exact aligned
  | cons op ops ih => exact ih _ (op.aligned base s aligned)

@[simp] theorem block_vector (base : BitVec 64) (ops : List Op) (s : ArmState)
    (reg : BitVec 5) : r (.SFP reg) (block base ops s) = r (.SFP reg) s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.vector base s reg)

end SszArm.Serialize

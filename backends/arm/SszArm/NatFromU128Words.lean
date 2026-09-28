import SszArm.NatFromU128Ops
import SszArm.DelimitedIntegerFacts
import SszArm.UintShifts

namespace SszArm.NatFromU128

theorem word_p0 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb50002c3#32)
    (hp : read_pc s = base + 0#64)
    : stepi s = Op.p0.effect base s := by
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  change r .PC s = _ at hp
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask, hp, hz]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p4 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xd10043ff#32)
    : stepi s = Op.p4.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p8 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf90003e9#32)
    : stepi s = Op.p8.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p12 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf90007ea#32)
    : stepi s = Op.p12.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p16 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x91000009#32)
    : stepi s = Op.p16.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p20 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xd280000a#32)
    : stepi s = Op.p20.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p24 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf900012a#32)
    : stepi s = Op.p24.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p28 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf9000522#32)
    : stepi s = Op.p28.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p32 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf94007ea#32)
    : stepi s = Op.p32.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p36 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf94003e9#32)
    : stepi s = Op.p36.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p40 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x910043ff#32)
    : stepi s = Op.p40.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p60 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x91010129#32)
    : stepi s = Op.p60.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p64 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x5280000a#32)
    : stepi s = Op.p64.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p68 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb900012a#32)
    : stepi s = Op.p68.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p84 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xd65f03c0#32)
    : stepi s = Op.p84.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p88 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf9400089#32)
    : stepi s = Op.p88.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p92 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf9400888#32)
    : stepi s = Op.p92.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p96 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xab09010a#32)
    : stepi s = Op.p96.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p100 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x540003c2#32)
    (hp : read_pc s = base + 100#64)
    : stepi s = Op.p100.effect base s := by
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  change r .PC s = _ at hp
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask, hp, hz]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p104 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb100215f#32)
    : stepi s = Op.p104.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p108 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54000388#32)
    (hp : read_pc s = base + 108#64)
    : stepi s = Op.p108.effect base s := by
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  change r .PC s = _ at hp
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask, hp, hz]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p112 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x91001d4b#32)
    : stepi s = Op.p112.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p116 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x927df16b#32)
    : stepi s = Op.p116.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p120 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xcb0a016a#32)
    : stepi s = Op.p120.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p124 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xab08014a#32)
    : stepi s = Op.p124.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p128 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x540002e2#32)
    (hp : read_pc s = base + 128#64)
    : stepi s = Op.p128.effect base s := by
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  change r .PC s = _ at hp
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask, hp, hz]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p132 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb100455f#32)
    : stepi s = Op.p132.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p136 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x540002a8#32)
    (hp : read_pc s = base + 136#64)
    : stepi s = Op.p136.effect base s := by
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  change r .PC s = _ at hp
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask, hp, hz]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p140 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf9400488#32)
    : stepi s = Op.p140.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p144 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x9100414b#32)
    : stepi s = Op.p144.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p148 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xeb08017f#32)
    : stepi s = Op.p148.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p152 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54000228#32)
    (hp : read_pc s = base + 152#64)
    : stepi s = Op.p152.effect base s := by
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  change r .PC s = _ at hp
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask, hp, hz]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p156 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x8b0a0129#32)
    : stepi s = Op.p156.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p160 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf900088b#32)
    : stepi s = Op.p160.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p164 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xa9000d22#32)
    : stepi s = Op.p164.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p168 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x52800042#32)
    : stepi s = Op.p168.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p172 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xa9000809#32)
    : stepi s = Op.p172.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p220 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x52900008#32)
    : stepi s = Op.p220.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p224 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x52800029#32)
    : stepi s = Op.p224.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p244 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x9100c129#32)
    : stepi s = Op.p244.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p260 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf900052a#32)
    : stepi s = Op.p260.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p292 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x91008129#32)
    : stepi s = Op.p292.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p340 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x91004129#32)
    : stepi s = Op.p340.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p376 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf90003ea#32)
    : stepi s = Op.p376.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p380 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf90007eb#32)
    : stepi s = Op.p380.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p384 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x9100000a#32)
    : stepi s = Op.p384.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p388 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf9000149#32)
    : stepi s = Op.p388.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p392 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xd280000b#32)
    : stepi s = Op.p392.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p396 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf900054b#32)
    : stepi s = Op.p396.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p400 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf94007eb#32)
    : stepi s = Op.p400.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p404 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf94003ea#32)
    : stepi s = Op.p404.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p412 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb9004008#32)
    : stepi s = Op.p412.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
     bitvec_rules, minimal_theory, BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha,
     BitVec.add_assoc, apply_ite, BoolCodec.pair_read_low, BoolCodec.pair_read_high,
     Delimited.and_ones64, Delimited.lsr61_mask, UintCodec.uint_lsl3_mask]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

end SszArm.NatFromU128

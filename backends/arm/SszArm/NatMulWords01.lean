import SszArm.NatMulOps
import SszArm.DelimitedExecCommon
import SszArm.UintShifts

namespace SszArm.NatMul

open UintCodec

theorem word_p80 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xd100052a#32) :
    stepi s = Op.p80.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next,
     exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, uint_lsl3_mask, uint_and_ones]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p84 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb4fffeab#32)
    (hp : read_pc s = base + 84#64) :
    stepi s = Op.p84.effect base s := by
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  change r .PC s = _ at hp
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next,
     exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, uint_lsl3_mask, uint_and_ones, hp, hz]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p88 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x91000555#32) :
    stepi s = Op.p88.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next,
     exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, uint_lsl3_mask, uint_and_ones]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p92 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa0203e8#32) :
    stepi s = Op.p92.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next,
     exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, uint_lsl3_mask, uint_and_ones]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p96 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb5000203#32)
    (hp : read_pc s = base + 96#64) :
    stepi s = Op.p96.effect base s := by
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  change r .PC s = _ at hp
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next,
     exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, uint_lsl3_mask, uint_and_ones, hp, hz]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p100 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x14000009#32)
    (hp : read_pc s = base + 100#64) :
    stepi s = Op.p100.effect base s := by
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  change r .PC s = _ at hp
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next,
     exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, uint_lsl3_mask, uint_and_ones, hp, hz]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p104 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb4000162#32)
    (hp : read_pc s = base + 104#64) :
    stepi s = Op.p104.effect base s := by
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  change r .PC s = _ at hp
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next,
     exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, uint_lsl3_mask, uint_and_ones, hp, hz]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p108 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb4000103#32)
    (hp : read_pc s = base + 108#64) :
    stepi s = Op.p108.effect base s := by
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  change r .PC s = _ at hp
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next,
     exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, uint_lsl3_mask, uint_and_ones, hp, hz]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p112 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x52800035#32) :
    stepi s = Op.p112.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next,
     exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, uint_lsl3_mask, uint_and_ones]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p120 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x1400000a#32)
    (hp : read_pc s = base + 120#64) :
    stepi s = Op.p120.effect base s := by
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  change r .PC s = _ at hp
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next,
     exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, uint_lsl3_mask, uint_and_ones, hp, hz]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p124 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa1f03f5#32) :
    stepi s = Op.p124.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next,
     exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, uint_lsl3_mask, uint_and_ones]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p132 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb50000e3#32)
    (hp : read_pc s = base + 132#64) :
    stepi s = Op.p132.effect base s := by
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  change r .PC s = _ at hp
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next,
     exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, uint_lsl3_mask, uint_and_ones, hp, hz]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p136 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb4000409#32)
    (hp : read_pc s = base + 136#64) :
    stepi s = Op.p136.effect base s := by
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  change r .PC s = _ at hp
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next,
     exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, uint_lsl3_mask, uint_and_ones, hp, hz]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p140 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb50002c4#32)
    (hp : read_pc s = base + 140#64) :
    stepi s = Op.p140.effect base s := by
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  change r .PC s = _ at hp
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next,
     exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, uint_lsl3_mask, uint_and_ones, hp, hz]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p144 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x1400001e#32)
    (hp : read_pc s = base + 144#64) :
    stepi s = Op.p144.effect base s := by
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  change r .PC s = _ at hp
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next,
     exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, uint_lsl3_mask, uint_and_ones, hp, hz]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p148 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb40003a3#32)
    (hp : read_pc s = base + 148#64) :
    stepi s = Op.p148.effect base s := by
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  change r .PC s = _ at hp
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next,
     exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, uint_lsl3_mask, uint_and_ones, hp, hz]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p152 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa1f03e8#32) :
    stepi s = Op.p152.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next,
     exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, uint_lsl3_mask, uint_and_ones]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p160 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa0403e9#32) :
    stepi s = Op.p160.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next,
     exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, uint_lsl3_mask, uint_and_ones]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p164 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb4000329#32)
    (hp : read_pc s = base + 164#64) :
    stepi s = Op.p164.effect base s := by
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  change r .PC s = _ at hp
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next,
     exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, uint_lsl3_mask, uint_and_ones, hp, hz]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p168 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa0903f6#32) :
    stepi s = Op.p168.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, Udivti3.compare, Udivti3.next,
     exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, uint_lsl3_mask, uint_and_ones]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

end SszArm.NatMul

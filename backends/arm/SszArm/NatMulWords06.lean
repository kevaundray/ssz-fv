import SszArm.NatMulOps
import SszArm.DelimitedExecCommon
import SszArm.UintShifts

namespace SszArm.NatMul

open UintCodec

theorem word_p588 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa1a03e9#32) :
    stepi s = Op.p588.effect base s := by
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

theorem word_p592 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa1f03ec#32) :
    stepi s = Op.p592.effect base s := by
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

theorem word_p596 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa1403eb#32) :
    stepi s = Op.p596.effect base s := by
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

theorem word_p600 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb4000189#32)
    (hp : read_pc s = base + 600#64) :
    stepi s = Op.p600.effect base s := by
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

theorem word_p604 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xeb0a019f#32) :
    stepi s = Op.p604.effect base s := by
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

theorem word_p608 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x540001a2#32)
    (hp : read_pc s = base + 608#64) :
    stepi s = Op.p608.effect base s := by
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

theorem word_p620 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa0c03ea#32) :
    stepi s = Op.p620.effect base s := by
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

theorem word_p628 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x8b0a012a#32) :
    stepi s = Op.p628.effect base s := by
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

theorem word_p632 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf940014e#32) :
    stepi s = Op.p632.effect base s := by
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

theorem word_p644 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x14000005#32)
    (hp : read_pc s = base + 644#64) :
    stepi s = Op.p644.effect base s := by
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

theorem word_p648 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf100019f#32) :
    stepi s = Op.p648.effect base s := by
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

theorem word_p652 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x9a9f014e#32) :
    stepi s = Op.p652.effect base s := by
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

theorem word_p656 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x14000002#32)
    (hp : read_pc s = base + 656#64) :
    stepi s = Op.p656.effect base s := by
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

theorem word_p660 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa1f03ee#32) :
    stepi s = Op.p660.effect base s := by
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

theorem word_p664 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa1f03f0#32) :
    stepi s = Op.p664.effect base s := by
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

theorem word_p668 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa1f03ef#32) :
    stepi s = Op.p668.effect base s := by
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

theorem word_p672 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa1f03f1#32) :
    stepi s = Op.p672.effect base s := by
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

theorem word_p676 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x9100058d#32) :
    stepi s = Op.p676.effect base s := by
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

theorem word_p680 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x8b100180#32) :
    stepi s = Op.p680.effect base s := by
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

theorem word_p684 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xeb13001f#32) :
    stepi s = Op.p684.effect base s := by
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

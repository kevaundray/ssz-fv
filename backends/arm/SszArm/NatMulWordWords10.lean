import SszArm.NatMulWordOps
import SszArm.DelimitedExecCommon
import SszArm.UintShifts

namespace SszArm.NatMulWord

open UintCodec

theorem word_p1472 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54000240#32)
    (hp : read_pc s = base + 1472#64) :
    stepi s = Op.p1472.effect base s := by
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

theorem word_p1476 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf85f8509#32) :
    stepi s = Op.p1476.effect base s := by
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

theorem word_p1480 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb4ffffa9#32)
    (hp : read_pc s = base + 1480#64) :
    stepi s = Op.p1480.effect base s := by
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

theorem word_p1484 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf100059f#32) :
    stepi s = Op.p1484.effect base s := by
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

theorem word_p1488 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x9a8c0168#32) :
    stepi s = Op.p1488.effect base s := by
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

theorem word_p1492 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x9a8a03e9#32) :
    stepi s = Op.p1492.effect base s := by
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

theorem word_p1496 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xa9002009#32) :
    stepi s = Op.p1496.effect base s := by
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

end SszArm.NatMulWord

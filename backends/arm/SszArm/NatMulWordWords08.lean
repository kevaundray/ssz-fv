import SszArm.NatMulWordOps
import SszArm.DelimitedExecCommon
import SszArm.UintShifts

namespace SszArm.NatMulWord

open UintCodec

theorem word_p1004 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x8b0f01ce#32) :
    stepi s = Op.p1004.effect base s := by
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

theorem word_p1008 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa0e03e9#32) :
    stepi s = Op.p1008.effect base s := by
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

theorem word_p1016 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf94013ee#32) :
    stepi s = Op.p1016.effect base s := by
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

theorem word_p1020 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf9400fed#32) :
    stepi s = Op.p1020.effect base s := by
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

theorem word_p1024 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf9400bec#32) :
    stepi s = Op.p1024.effect base s := by
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

theorem word_p1028 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf94007eb#32) :
    stepi s = Op.p1028.effect base s := by
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

theorem word_p1032 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf94003ea#32) :
    stepi s = Op.p1032.effect base s := by
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

theorem word_p1040 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x9b037c48#32) :
    stepi s = Op.p1040.effect base s := by
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

theorem word_p1044 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb50002c9#32)
    (hp : read_pc s = base + 1044#64) :
    stepi s = Op.p1044.effect base s := by
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

theorem word_p1072 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf9000528#32) :
    stepi s = Op.p1072.effect base s := by
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

theorem word_p1136 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf940088b#32) :
    stepi s = Op.p1136.effect base s := by
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

theorem word_p1140 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xab0a016c#32) :
    stepi s = Op.p1140.effect base s := by
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

theorem word_p1144 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x540003c2#32)
    (hp : read_pc s = base + 1144#64) :
    stepi s = Op.p1144.effect base s := by
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

theorem word_p1148 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb100219f#32) :
    stepi s = Op.p1148.effect base s := by
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

theorem word_p1152 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54000388#32)
    (hp : read_pc s = base + 1152#64) :
    stepi s = Op.p1152.effect base s := by
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

theorem word_p1156 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x91001d8d#32) :
    stepi s = Op.p1156.effect base s := by
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

theorem word_p1160 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x927df1ad#32) :
    stepi s = Op.p1160.effect base s := by
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

theorem word_p1164 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xcb0c01ac#32) :
    stepi s = Op.p1164.effect base s := by
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

theorem word_p1168 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xab0b018b#32) :
    stepi s = Op.p1168.effect base s := by
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

theorem word_p1172 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x540002e2#32)
    (hp : read_pc s = base + 1172#64) :
    stepi s = Op.p1172.effect base s := by
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

end SszArm.NatMulWord

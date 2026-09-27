import SszArm.DelimitedExecCommon

namespace SszArm.Delimited

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem word_p0 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb4000623#32)
    (hp : read_pc s = base + 0#64)
    : stepi s = Op.p0.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 0#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p60 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x340003e8#32)
    (hp : read_pc s = base + 60#64)
    : stepi s = Op.p60.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 60#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p100 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x34000089#32)
    (hp : read_pc s = base + 100#64)
    : stepi s = Op.p100.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 100#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p112 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x35ffffc9#32)
    (hp : read_pc s = base + 112#64)
    : stepi s = Op.p112.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 112#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p144 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x540003e2#32)
    (hp : read_pc s = base + 144#64)
    : stepi s = Op.p144.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 144#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p164 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54000640#32)
    (hp : read_pc s = base + 164#64)
    : stepi s = Op.p164.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 164#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p168 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x1400005d#32)
    (hp : read_pc s = base + 168#64)
    : stepi s = Op.p168.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 168#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p180 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x35000da8#32)
    (hp : read_pc s = base + 180#64)
    : stepi s = Op.p180.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 180#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p184 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb5ffffa3#32)
    (hp : read_pc s = base + 184#64)
    : stepi s = Op.p184.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 184#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p192 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x1400006b#32)
    (hp : read_pc s = base + 192#64)
    : stepi s = Op.p192.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 192#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p264 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xd65f03c0#32)
    (hp : read_pc s = base + 264#64)
    : stepi s = Op.p264.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 264#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p280 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54000ec2#32)
    (hp : read_pc s = base + 280#64)
    : stepi s = Op.p280.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 280#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p288 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54000e88#32)
    (hp : read_pc s = base + 288#64)
    : stepi s = Op.p288.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 288#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s ≠ 1#1) ↔ r (.FLAG .Z) s = 0#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hz0, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p308 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54000de2#32)
    (hp : read_pc s = base + 308#64)
    : stepi s = Op.p308.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 308#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p316 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54000da8#32)
    (hp : read_pc s = base + 316#64)
    : stepi s = Op.p316.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 316#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s ≠ 1#1) ↔ r (.FLAG .Z) s = 0#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hz0, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p332 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54000d28#32)
    (hp : read_pc s = base + 332#64)
    : stepi s = Op.p332.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 332#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s ≠ 1#1) ↔ r (.FLAG .Z) s = 0#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hz0, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p360 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x540005a1#32)
    (hp : read_pc s = base + 360#64)
    : stepi s = Op.p360.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 360#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p396 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x97ffbb50#32)
    (hp : read_pc s = base + 396#64)
    : stepi s = Op.p396.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 396#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p420 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x540003cb#32)
    (hp : read_pc s = base + 420#64)
    : stepi s = Op.p420.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 420#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p536 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x1400005f#32)
    (hp : read_pc s = base + 536#64)
    : stepi s = Op.p536.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 536#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p544 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54000061#32)
    (hp : read_pc s = base + 544#64)
    : stepi s = Op.p544.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 544#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p552 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x14000002#32)
    (hp : read_pc s = base + 552#64)
    : stepi s = Op.p552.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 552#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p568 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54000062#32)
    (hp : read_pc s = base + 568#64)
    : stepi s = Op.p568.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 568#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p576 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x14000002#32)
    (hp : read_pc s = base + 576#64)
    : stepi s = Op.p576.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 576#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p592 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb50002e8#32)
    (hp : read_pc s = base + 592#64)
    : stepi s = Op.p592.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 592#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p612 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x1400005c#32)
    (hp : read_pc s = base + 612#64)
    : stepi s = Op.p612.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 612#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p680 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x1400004a#32)
    (hp : read_pc s = base + 680#64)
    : stepi s = Op.p680.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 680#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p748 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x14000039#32)
    (hp : read_pc s = base + 748#64)
    : stepi s = Op.p748.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 748#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

theorem word_p1008 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xd65f03c0#32)
    (hp : read_pc s = base + 1008#64)
    : stepi s = Op.p1008.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 1008#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, lsr61_mask, lsr1_mask, lsl24_mask, hpc, hz, hcarry, compareOffset]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

end SszArm.Delimited

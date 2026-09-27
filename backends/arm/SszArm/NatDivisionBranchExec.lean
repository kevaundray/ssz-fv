import SszArm.NatDivisionOps

namespace SszArm.NatDivision

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem word_p32 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb4000861#32)
    (hp : read_pc s = base + 32#64)
    : stepi s = Op.p32.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 32#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p44 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x540008e0#32)
    (hp : read_pc s = base + 44#64)
    : stepi s = Op.p44.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 44#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p88 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb4fffe8a#32)
    (hp : read_pc s = base + 88#64)
    : stepi s = Op.p88.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 88#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p100 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54000743#32)
    (hp : read_pc s = base + 100#64)
    : stepi s = Op.p100.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 100#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p128 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54001c20#32)
    (hp : read_pc s = base + 128#64)
    : stepi s = Op.p128.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 128#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p164 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb4fffeaa#32)
    (hp : read_pc s = base + 164#64)
    : stepi s = Op.p164.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 164#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p172 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb5001409#32)
    (hp : read_pc s = base + 172#64)
    : stepi s = Op.p172.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 172#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p192 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb500008a#32)
    (hp : read_pc s = base + 192#64)
    : stepi s = Op.p192.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 192#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p204 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x14000004#32)
    (hp : read_pc s = base + 204#64)
    : stepi s = Op.p204.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 204#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p216 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x14000095#32)
    (hp : read_pc s = base + 216#64)
    : stepi s = Op.p216.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 216#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p232 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54001222#32)
    (hp : read_pc s = base + 232#64)
    : stepi s = Op.p232.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 232#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p240 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x540011e8#32)
    (hp : read_pc s = base + 240#64)
    : stepi s = Op.p240.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 240#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p260 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54001142#32)
    (hp : read_pc s = base + 260#64)
    : stepi s = Op.p260.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 260#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p268 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54001102#32)
    (hp : read_pc s = base + 268#64)
    : stepi s = Op.p268.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 268#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p280 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x540010a8#32)
    (hp : read_pc s = base + 280#64)
    : stepi s = Op.p280.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 280#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p296 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x14000027#32)
    (hp : read_pc s = base + 296#64)
    : stepi s = Op.p296.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 296#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p316 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x9400b213#32)
    (hp : read_pc s = base + 316#64)
    : stepi s = Op.p316.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 316#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p320 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb4000a21#32)
    (hp : read_pc s = base + 320#64)
    : stepi s = Op.p320.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 320#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p324 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x1400005a#32)
    (hp : read_pc s = base + 324#64)
    : stepi s = Op.p324.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 324#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p328 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb4000a42#32)
    (hp : read_pc s = base + 328#64)
    : stepi s = Op.p328.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 328#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p340 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x540008c3#32)
    (hp : read_pc s = base + 340#64)
    : stepi s = Op.p340.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 340#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p360 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x9400b208#32)
    (hp : read_pc s = base + 360#64)
    : stepi s = Op.p360.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 360#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p364 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb40008c1#32)
    (hp : read_pc s = base + 364#64)
    : stepi s = Op.p364.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 364#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p368 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x1400004f#32)
    (hp : read_pc s = base + 368#64)
    : stepi s = Op.p368.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 368#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p448 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54000240#32)
    (hp : read_pc s = base + 448#64)
    : stepi s = Op.p448.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 448#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p456 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54fffd63#32)
    (hp : read_pc s = base + 456#64)
    : stepi s = Op.p456.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 456#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p516 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54fffe01#32)
    (hp : read_pc s = base + 516#64)
    : stepi s = Op.p516.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 516#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p564 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x9400b1d5#32)
    (hp : read_pc s = base + 564#64)
    : stepi s = Op.p564.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 564#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p612 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54fffd41#32)
    (hp : read_pc s = base + 612#64)
    : stepi s = Op.p612.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 612#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p616 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x14000068#32)
    (hp : read_pc s = base + 616#64)
    : stepi s = Op.p616.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 616#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p636 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x9400b1c3#32)
    (hp : read_pc s = base + 636#64)
    : stepi s = Op.p636.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 636#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p640 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb5000161#32)
    (hp : read_pc s = base + 640#64)
    : stepi s = Op.p640.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 640#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p652 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x1400001d#32)
    (hp : read_pc s = base + 652#64)
    : stepi s = Op.p652.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 652#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p676 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x9400b1b9#32)
    (hp : read_pc s = base + 676#64)
    : stepi s = Op.p676.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 676#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p680 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb4fffee1#32)
    (hp : read_pc s = base + 680#64)
    : stepi s = Op.p680.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 680#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p696 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x540003a2#32)
    (hp : read_pc s = base + 696#64)
    : stepi s = Op.p696.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 696#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p704 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54000368#32)
    (hp : read_pc s = base + 704#64)
    : stepi s = Op.p704.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 704#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p724 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x540002c2#32)
    (hp : read_pc s = base + 724#64)
    : stepi s = Op.p724.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 724#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p732 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54000288#32)
    (hp : read_pc s = base + 732#64)
    : stepi s = Op.p732.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 732#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p748 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54000208#32)
    (hp : read_pc s = base + 748#64)
    : stepi s = Op.p748.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 748#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p808 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x1400002a#32)
    (hp : read_pc s = base + 808#64)
    : stepi s = Op.p808.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 808#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p1024 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xd65f03c0#32)
    (hp : read_pc s = base + 1024#64)
    : stepi s = Op.p1024.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 1024#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p1040 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x54000220#32)
    (hp : read_pc s = base + 1040#64)
    : stepi s = Op.p1040.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 1040#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p1084 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb4fffe8a#32)
    (hp : read_pc s = base + 1084#64)
    : stepi s = Op.p1084.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 1084#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p1096 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x540000a1#32)
    (hp : read_pc s = base + 1096#64)
    : stepi s = Op.p1096.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 1096#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p1104 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x14000002#32)
    (hp : read_pc s = base + 1104#64)
    : stepi s = Op.p1104.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 1104#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

theorem word_p1124 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x17ffffaf#32)
    (hp : read_pc s = base + 1124#64)
    : stepi s = Op.p1124.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  have hpc : r .PC s = base + 1124#64 := hp
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  have hz0 : (r (.FLAG .Z) s = 0#1) ↔ r (.FLAG .Z) s ≠ 1#1 := by bv_omega
  have hcarry : (r (.FLAG .C) s ≠ 0#1) ↔ r (.FLAG .C) s = 1#1 := by bv_omega
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
     BitVec.setWidth_eq, BitVec.sub_eq_add_neg, ha, BitVec.add_assoc, apply_ite,
     BoolCodec.pair_read_low, BoolCodec.pair_read_high, hpc, hz, hz0, hcarry ]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

end SszArm.NatDivision

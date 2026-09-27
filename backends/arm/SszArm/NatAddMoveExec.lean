import SszArm.NatAddOps
import SszArm.DelimitedExecCommon
import SszArm.UintShifts

namespace SszArm.NatAdd

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The actual word at +8: `mov x10, x2`. -/
theorem word_p8 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa0203ea#32)
    : stepi s = Op.p8.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +12: `mov x9, x10`. -/
theorem word_p12 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa0a03e9#32)
    : stepi s = Op.p12.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +28: `mov x10, x9`. -/
theorem word_p28 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa0903ea#32)
    : stepi s = Op.p28.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +80: `mov w8, #1`. -/
theorem word_p80 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x52800028#32)
    : stepi s = Op.p80.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +88: `mov x8, xzr`. -/
theorem word_p88 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa1f03e8#32)
    : stepi s = Op.p88.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +100: `mov x3, xzr`. -/
theorem word_p100 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa1f03e3#32)
    : stepi s = Op.p100.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +108: `mov w9, wzr`. -/
theorem word_p108 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x2a1f03e9#32)
    : stepi s = Op.p108.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +112: `mov w10, #1`. -/
theorem word_p112 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x5280002a#32)
    : stepi s = Op.p112.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +144: `mov x9, #0x1ffffffffffffffe`. -/
theorem word_p144 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb27fefe9#32)
    : stepi s = Op.p144.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +304: `mov x11, x9`. -/
theorem word_p304 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa0903eb#32)
    : stepi s = Op.p304.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr]

/-- The actual word at +324: `mov x9, x11`. -/
theorem word_p324 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa0b03e9#32)
    : stepi s = Op.p324.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +348: `mov x10, x11`. -/
theorem word_p348 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa0b03ea#32)
    : stepi s = Op.p348.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +368: `mov w9, #1`. -/
theorem word_p368 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x52800029#32)
    : stepi s = Op.p368.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +448: `mov x8, x9`. -/
theorem word_p448 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa0903e8#32)
    : stepi s = Op.p448.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +516: `mov w10, #0`. -/
theorem word_p516 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x5280000a#32)
    : stepi s = Op.p516.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +552: `mov x8, #0`. -/
theorem word_p552 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xd2800008#32)
    : stepi s = Op.p552.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +560: `mov x8, #1`. -/
theorem word_p560 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xd2800028#32)
    : stepi s = Op.p560.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +652: `mov x1, xzr`. -/
theorem word_p652 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa1f03e1#32)
    : stepi s = Op.p652.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +720: `mov x10, #0`. -/
theorem word_p720 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xd280000a#32)
    : stepi s = Op.p720.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +988: `mov x8, x8`. -/
theorem word_p988 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa0803e8#32)
    : stepi s = Op.p988.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1020: `mov x11, #0`. -/
theorem word_p1020 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xd280000b#32)
    : stepi s = Op.p1020.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1096: `mov x8, x2`. -/
theorem word_p1096 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa0203e8#32)
    : stepi s = Op.p1096.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1196: `mov w9, #2`. -/
theorem word_p1196 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x52800049#32)
    : stepi s = Op.p1196.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1436: `mov w8, #0x8000`. -/
theorem word_p1436 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x52900008#32)
    : stepi s = Op.p1436.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1452: `mov x12, xzr`. -/
theorem word_p1452 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa1f03ec#32)
    : stepi s = Op.p1452.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1456: `mov x11, x2`. -/
theorem word_p1456 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa0203eb#32)
    : stepi s = Op.p1456.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1464: `mov x11, xzr`. -/
theorem word_p1464 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa1f03eb#32)
    : stepi s = Op.p1464.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1492: `mov w13, wzr`. -/
theorem word_p1492 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x2a1f03ed#32)
    : stepi s = Op.p1492.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1500: `mov w12, #0`. -/
theorem word_p1500 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x5280000c#32)
    : stepi s = Op.p1500.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1508: `mov w12, #1`. -/
theorem word_p1508 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x5280002c#32)
    : stepi s = Op.p1508.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1520: `mov x13, xzr`. -/
theorem word_p1520 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa1f03ed#32)
    : stepi s = Op.p1520.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1532: `mov x12, x12`. -/
theorem word_p1532 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa0c03ec#32)
    : stepi s = Op.p1532.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1552: `mov w13, #1`. -/
theorem word_p1552 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x5280002d#32)
    : stepi s = Op.p1552.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1556: `mov w15, #1`. -/
theorem word_p1556 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x5280002f#32)
    : stepi s = Op.p1556.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1564: `mov x14, x8`. -/
theorem word_p1564 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa0803ee#32)
    : stepi s = Op.p1564.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1580: `mov x9, x15`. -/
theorem word_p1580 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa0f03e9#32)
    : stepi s = Op.p1580.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1612: `mov w17, #0`. -/
theorem word_p1612 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x52800011#32)
    : stepi s = Op.p1612.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1620: `mov w17, #1`. -/
theorem word_p1620 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x52800031#32)
    : stepi s = Op.p1620.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1636: `mov x10, x15`. -/
theorem word_p1636 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa0f03ea#32)
    : stepi s = Op.p1636.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1664: `mov x12, x17`. -/
theorem word_p1664 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa1103ec#32)
    : stepi s = Op.p1664.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1684: `mov x15, x17`. -/
theorem word_p1684 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa1103ef#32)
    : stepi s = Op.p1684.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1748: `mov w17, w13`. -/
theorem word_p1748 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x2a0d03f1#32)
    : stepi s = Op.p1748.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1796: `mov x16, xzr`. -/
theorem word_p1796 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa1f03f0#32)
    : stepi s = Op.p1796.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1860: `mov x17, xzr`. -/
theorem word_p1860 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa1f03f1#32)
    : stepi s = Op.p1860.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1868: `mov w14, #1`. -/
theorem word_p1868 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x5280002e#32)
    : stepi s = Op.p1868.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1872: `mov x13, x8`. -/
theorem word_p1872 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa0803ed#32)
    : stepi s = Op.p1872.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1888: `mov x9, x14`. -/
theorem word_p1888 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa0e03e9#32)
    : stepi s = Op.p1888.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1928: `mov x10, x14`. -/
theorem word_p1928 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa0e03ea#32)
    : stepi s = Op.p1928.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1972: `mov x14, x16`. -/
theorem word_p1972 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa1003ee#32)
    : stepi s = Op.p1972.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1988: `mov x15, xzr`. -/
theorem word_p1988 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xaa1f03ef#32)
    : stepi s = Op.p1988.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +2012: `mov w13, #0`. -/
theorem word_p2012 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x5280000d#32)
    : stepi s = Op.p2012.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

end SszArm.NatAdd

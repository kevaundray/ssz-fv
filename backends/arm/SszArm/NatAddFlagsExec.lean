import SszArm.NatAddOps
import SszArm.DelimitedExecCommon
import SszArm.UintShifts

namespace SszArm.NatAdd

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

private theorem gpr_pstate_commute (s : ArmState) (reg : BitVec 5)
    (value : BitVec 64) (flags : PState) :
    w (.GPR reg) value (write_pstate flags s) =
      write_pstate flags (w (.GPR reg) value s) := by
  simp [write_pstate, w, write_base_gpr, write_base_flag]

/-- The actual word at +120: `cmp x11, #2`. -/
theorem word_p120 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf100097f#32)
    : stepi s = Op.p120.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +128: `cmp x10, x8`. -/
theorem word_p128 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xeb08015f#32)
    : stepi s = Op.p128.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +132: `csel x8, x10, x8, hi`. -/
theorem word_p132 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x9a888148#32)
    : stepi s = Op.p132.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +136: `cmn x8, #1`. -/
theorem word_p136 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb100051f#32)
    : stepi s = Op.p136.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +148: `cmp x8, x9`. -/
theorem word_p148 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xeb09011f#32)
    : stepi s = Op.p148.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +212: `adds x13, x12, x9`. -/
theorem word_p212 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xab09018d#32)
    : stepi s = Op.p212.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +220: `cmn x13, #8`. -/
theorem word_p220 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb10021bf#32)
    : stepi s = Op.p220.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +240: `adds x12, x13, x12`. -/
theorem word_p240 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xab0c01ac#32)
    : stepi s = Op.p240.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +248: `adds x11, x12, x11`. -/
theorem word_p248 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xab0b018b#32)
    : stepi s = Op.p248.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +260: `cmp x11, x13`. -/
theorem word_p260 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xeb0d017f#32)
    : stepi s = Op.p260.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +308: `cmn x11, #1`. -/
theorem word_p308 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb100057f#32)
    : stepi s = Op.p308.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +460: `cmn x9, #1`. -/
theorem word_p460 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb100053f#32)
    : stepi s = Op.p460.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +476: `cmp x4, #1`. -/
theorem word_p476 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf100049f#32)
    : stepi s = Op.p476.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +544: `adds x9, x2, x4`. -/
theorem word_p544 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xab040049#32)
    : stepi s = Op.p544.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +640: `cmp x2, #1`. -/
theorem word_p640 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf100045f#32)
    : stepi s = Op.p640.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1120: `adds x11, x10, x8`. -/
theorem word_p1120 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xab08014b#32)
    : stepi s = Op.p1120.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1128: `cmn x11, #8`. -/
theorem word_p1128 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb100217f#32)
    : stepi s = Op.p1128.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1148: `adds x10, x11, x10`. -/
theorem word_p1148 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xab0a016a#32)
    : stepi s = Op.p1148.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1156: `cmn x10, #0x11`. -/
theorem word_p1156 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xb100455f#32)
    : stepi s = Op.p1156.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1172: `cmp x11, x12`. -/
theorem word_p1172 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xeb0c017f#32)
    : stepi s = Op.p1172.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1488: `adds x11, x11, x4`. -/
theorem word_p1488 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xab04016b#32)
    : stepi s = Op.p1488.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1524: `adds x11, x11, x13`. -/
theorem word_p1524 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xab0d016b#32)
    : stepi s = Op.p1524.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1604: `adds x12, x12, x17`. -/
theorem word_p1604 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xab11018c#32)
    : stepi s = Op.p1604.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1624: `adds x16, x12, x16`. -/
theorem word_p1624 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xab100190#32)
    : stepi s = Op.p1624.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1680: `subs x14, x14, #1`. -/
theorem word_p1680 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf10005ce#32)
    : stepi s = Op.p1680.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true}) only
    [Op.effect, put, next, exec_inst, DPI.exec_add_sub_imm,
     read_gpr, write_gpr_zr, write_gpr, write_pc, BitVec.setWidth_eq,
     bitvec_rules, minimal_theory]
  exact gpr_pstate_commute _ _ _ _

/-- The actual word at +1692: `cmp x15, x2`. -/
theorem word_p1692 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xeb0201ff#32)
    : stepi s = Op.p1692.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1732: `cmp x15, x4`. -/
theorem word_p1732 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xeb0401ff#32)
    : stepi s = Op.p1732.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1912: `adds x15, x12, x15`. -/
theorem word_p1912 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xab0f018f#32)
    : stepi s = Op.p1912.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1968: `subs x13, x13, #1`. -/
theorem word_p1968 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf10005ad#32)
    : stepi s = Op.p1968.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true}) only
    [Op.effect, put, next, exec_inst, DPI.exec_add_sub_imm,
     read_gpr, write_gpr_zr, write_gpr, write_pc, BitVec.setWidth_eq,
     bitvec_rules, minimal_theory]
  exact gpr_pstate_commute _ _ _ _

/-- The actual word at +1980: `cmp x14, x4`. -/
theorem word_p1980 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xeb0401df#32)
    : stepi s = Op.p1980.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +1996: `adds x11, x2, x4`. -/
theorem word_p1996 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xab04004b#32)
    : stepi s = Op.p1996.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +2052: `subs x8, x8, #1`. -/
theorem word_p2052 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf1000508#32)
    : stepi s = Op.p2052.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true}) only
    [Op.effect, put, next, exec_inst, DPI.exec_add_sub_imm,
     read_gpr, write_gpr_zr, write_gpr, write_pc, BitVec.setWidth_eq,
     bitvec_rules, minimal_theory]
  exact gpr_pstate_commute _ _ _ _

/-- The actual word at +2068: `cmp x8, #1`. -/
theorem word_p2068 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0xf100051f#32)
    : stepi s = Op.p2068.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +2072: `csel x8, x11, x8, eq`. -/
theorem word_p2072 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x9a880168#32)
    : stepi s = Op.p2072.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

/-- The actual word at +2076: `csel x9, xzr, x9, eq`. -/
theorem word_p2076 (s : ArmState) (base : BitVec 64)
    (he : read_err s = .None) (_ha : CheckSPAlignment s)
    (hf : s.program.find? (read_pc s) = some 0x9a8903e9#32)
    : stepi s = Op.p2076.effect base s := by
  rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he rfl
    (fetch_inst_from_program.trans hf) rfl]
  simp (config := {decide := true, instances := true})
    [Op.effect, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq, apply_ite]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all only [not_false_eq_true, not_true_eq_false, ↓reduceIte])
    | simp [w, write_base_pc, write_base_gpr, write_base_flag]

end SszArm.NatAdd

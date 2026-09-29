import SszArm.CodecLinkedPlanSingleton
import SszArm.MeasureActivationOps

set_option autoImplicit false

namespace SszArm.Codec.Measure.Singleton.Body

open SszArm.Measure.Activation (next put save)

inductive Op where
  | p92 | p96 | p100 | p108 | p112
  | p168 | p172 | p176 | p180 | p184 | p188 | p192 | p196 | p200 | p204 | p208 | p212
  | p216 | p220 | p224 | p228 | p232 | p236 | p240 | p244 | p248 | p252 | p256 | p260 | p264
  | p268 | p272 | p276 | p280 | p284 | p288 | p292 | p296 | p300 | p304 | p308 | p312 | p316
  | p320 | p324 | p328 | p332 | p336 | p340 | p344 | p348 | p352 | p356 | p360
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p92 => (92, 0xaa0203e1#32)
  | .p96 => (96, 0xaa1403e0#32)
  | .p100 => (100, 0x52800502#32)
  | .p108 => (108, 0x52800028#32)
  | .p112 => (112, 0xa9002274#32)
  | .p168 => (168, 0xd10043ff#32)
  | .p172 => (172, 0xf90003e9#32)
  | .p176 => (176, 0xf90007ea#32)
  | .p180 => (180, 0x91000269#32)
  | .p184 => (184, 0x9100c129#32)
  | .p188 => (188, 0xd280000a#32)
  | .p192 => (192, 0xf900012a#32)
  | .p196 => (196, 0xd280000a#32)
  | .p200 => (200, 0xf900052a#32)
  | .p204 => (204, 0xf94007ea#32)
  | .p208 => (208, 0xf94003e9#32)
  | .p212 => (212, 0x910043ff#32)
  | .p216 => (216, 0x52900009#32)
  | .p220 => (220, 0xd10043ff#32)
  | .p224 => (224, 0xf90003e9#32)
  | .p228 => (228, 0xf90007ea#32)
  | .p232 => (232, 0x91000269#32)
  | .p236 => (236, 0x91008129#32)
  | .p240 => (240, 0xd280000a#32)
  | .p244 => (244, 0xf900012a#32)
  | .p248 => (248, 0xd280000a#32)
  | .p252 => (252, 0xf900052a#32)
  | .p256 => (256, 0xf94007ea#32)
  | .p260 => (260, 0xf94003e9#32)
  | .p264 => (264, 0x910043ff#32)
  | .p268 => (268, 0x52800034#32)
  | .p272 => (272, 0xd10043ff#32)
  | .p276 => (276, 0xf90003e9#32)
  | .p280 => (280, 0xf90007ea#32)
  | .p284 => (284, 0x91000269#32)
  | .p288 => (288, 0x91004129#32)
  | .p292 => (292, 0xd280000a#32)
  | .p296 => (296, 0xf900012a#32)
  | .p300 => (300, 0xd280000a#32)
  | .p304 => (304, 0xf900052a#32)
  | .p308 => (308, 0xf94007ea#32)
  | .p312 => (312, 0xf94003e9#32)
  | .p316 => (316, 0x910043ff#32)
  | .p320 => (320, 0xd10043ff#32)
  | .p324 => (324, 0xf90003e9#32)
  | .p328 => (328, 0xf90007ea#32)
  | .p332 => (332, 0x91000269#32)
  | .p336 => (336, 0xf9000134#32)
  | .p340 => (340, 0xd280000a#32)
  | .p344 => (344, 0xf900052a#32)
  | .p348 => (348, 0xf94007ea#32)
  | .p352 => (352, 0xf94003e9#32)
  | .p356 => (356, 0x910043ff#32)
  | .p360 => (360, 0xb9004269#32)

def Op.effect : Op → ArmState → ArmState
  | .p92, s => put 1 (r (.GPR 2) s) s
  | .p96, s => put 0 (r (.GPR 20) s) s
  | .p100, s => put 2 40#64 s
  | .p108, s => put 8 1#64 s
  | .p112, s => next (write_mem_bytes 16 (r (.GPR 19) s) (r (.GPR 8) s ++ r (.GPR 20) s) s)
  | .p168, s | .p220, s | .p272, s | .p320, s => put 31 (r (.GPR 31) s - 16#64) s
  | .p172, s | .p224, s | .p276, s | .p324, s =>
      next (write_mem_bytes 8 (r (.GPR 31) s) (r (.GPR 9) s) s)
  | .p176, s | .p228, s | .p280, s | .p328, s =>
      next (write_mem_bytes 8 (r (.GPR 31) s + 8#64) (r (.GPR 10) s) s)
  | .p180, s | .p232, s | .p284, s | .p332, s => put 9 (r (.GPR 19) s) s
  | .p184, s => put 9 (r (.GPR 9) s + 48#64) s
  | .p236, s => put 9 (r (.GPR 9) s + 32#64) s
  | .p288, s => put 9 (r (.GPR 9) s + 16#64) s
  | .p188, s | .p196, s | .p240, s | .p248, s | .p292, s | .p300, s | .p340, s => put 10 0#64 s
  | .p192, s | .p244, s | .p296, s => next (write_mem_bytes 8 (r (.GPR 9) s) (r (.GPR 10) s) s)
  | .p200, s | .p252, s | .p304, s | .p344, s =>
      next (write_mem_bytes 8 (r (.GPR 9) s + 8#64) (r (.GPR 10) s) s)
  | .p204, s | .p256, s | .p308, s | .p348, s =>
      put 10 (read_mem_bytes 8 (r (.GPR 31) s + 8#64) s) s
  | .p208, s | .p260, s | .p312, s | .p352, s => put 9 (read_mem_bytes 8 (r (.GPR 31) s) s) s
  | .p212, s | .p264, s | .p316, s | .p356, s => put 31 (r (.GPR 31) s + 16#64) s
  | .p216, s => put 9 32768#64 s
  | .p268, s => put 20 1#64 s
  | .p336, s => next (write_mem_bytes 8 (r (.GPR 9) s) (r (.GPR 20) s) s)
  | .p360, s => next (write_mem_bytes 4 (r (.GPR 19) s + 64#64) ((r (.GPR 9) s).setWidth 32) s)

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.PlanSingleton.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect s := by
  have fetched := code op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [Op.effect, next, put, exec_inst, state_simp_rules, bitvec_rules,
       minimal_theory, aligned, BitVec.sub_eq_add_neg, BitVec.setWidth_eq]
  all_goals first | exact w_of_w_commute (by decide) | simp only [w, write_base_pc, write_base_gpr]

@[simp] theorem Op.program (op : Op) (s : ArmState) : (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, next, put, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) : read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, next, put, state_simp_rules]

def Preserved : StateField → Prop
  | .GPR reg => reg ∉ [0#5, 1#5, 2#5, 8#5, 9#5, 10#5, 20#5, 31#5]
  | .PC | .FLAG _ => False
  | _ => True

theorem Op.field (op : Op) (s : ArmState) (field : StateField) (preserved : Preserved field) :
    r field (op.effect s) = r field s := by
  cases field <;> simp only [Preserved] at preserved
  all_goals first | contradiction |
    (cases op <;> simp_all [Op.effect, next, put, state_simp_rules])

def block (ops : List Op) (s : ArmState) : ArmState := ops.foldl (fun t op => op.effect t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => CheckSPAlignment s ∧
      read_pc s = base + BitVec.ofNat 64 op.row.1 ∧ Follows base ops (op.effect s)

theorem runs (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.PlanSingleton.CodeAt s base) (error : read_err s = .None)
    (follows : Follows base ops s) : run ops.length s = block ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = block ops (op.effect s)
    rw [run, step op s base code error follows.1 follows.2.1]
    apply ih _ _ ((op.error s).trans error) follows.2.2
    intro row member
    simpa only [Op.program] using code row member

@[simp] theorem block_program (ops : List Op) (s : ArmState) : (block ops s).program = s.program := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.program s)

@[simp] theorem block_error (ops : List Op) (s : ArmState) : read_err (block ops s) = read_err s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.error s)

theorem block_field (ops : List Op) (s : ArmState) (field : StateField) (preserved : Preserved field) :
    r field (block ops s) = r field s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.field s field preserved)

end SszArm.Codec.Measure.Singleton.Body

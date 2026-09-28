import SszArm.NatToU128Impl
import SszArm.NatCompareExec

namespace SszArm.NatToU128

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

inductive Op where
  | p0 | p4 | p8 | p12 | p16 | p20 | p24 | p28 | p32 | p36 | p40 | p44
  | p48 | p52 | p56 | p60 | p64 | p68 | p72 | p76 | p80 | p84 | p88 | p92
  | p96 | p100 | p104 | p108 | p112 | p116 | p120 | p124 | p128 | p132 | p136 | p140
  | p144 | p148 | p152 | p156 | p160 | p164 | p168 | p172 | p176 | p180 | p184 | p188
  | p192 | p196 | p200 | p204 | p208 | p212 | p216 | p220 | p224 | p228 | p232 | p236
  | p240 | p244 | p248 | p252 | p256 | p260 | p264 | p268 | p272 | p276 | p280 | p284
  | p288 | p292 | p296 | p300 | p304 | p308 | p312 | p316 | p320 | p324 | p328 | p332
  | p336 | p340 | p344 | p348 | p352 | p356 | p360 | p364 | p368 | p372 | p376 | p380
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p0 => (0, 0xb4000621#32)
  | .p4 => (4, 0xd1000449#32)
  | .p8 => (8, 0xb100053f#32)
  | .p12 => (12, 0x54000360#32)
  | .p16 => (16, 0xd10043ff#32)
  | .p20 => (20, 0xf90003eb#32)
  | .p24 => (24, 0xaa0903eb#32)
  | .p28 => (28, 0xd37df16b#32)
  | .p32 => (32, 0x8b0b002b#32)
  | .p36 => (36, 0xf940016a#32)
  | .p40 => (40, 0xf94003eb#32)
  | .p44 => (44, 0x910043ff#32)
  | .p48 => (48, 0xaa0903e8#32)
  | .p52 => (52, 0xd1000529#32)
  | .p56 => (56, 0xb4fffe8a#32)
  | .p60 => (60, 0x91000508#32)
  | .p64 => (64, 0xf1000d1f#32)
  | .p68 => (68, 0x540001c3#32)
  | .p72 => (72, 0xd10043ff#32)
  | .p76 => (76, 0xf90003e9#32)
  | .p80 => (80, 0xf90007ea#32)
  | .p84 => (84, 0x91000009#32)
  | .p88 => (88, 0xd280000a#32)
  | .p92 => (92, 0xf900012a#32)
  | .p96 => (96, 0xd280000a#32)
  | .p100 => (100, 0xf900052a#32)
  | .p104 => (104, 0xf94007ea#32)
  | .p108 => (108, 0xf94003e9#32)
  | .p112 => (112, 0x910043ff#32)
  | .p116 => (116, 0xd65f03c0#32)
  | .p120 => (120, 0xb4000262#32)
  | .p124 => (124, 0xf9400028#32)
  | .p128 => (128, 0xf100085f#32)
  | .p132 => (132, 0x540004e3#32)
  | .p136 => (136, 0xf9400429#32)
  | .p140 => (140, 0xaa0803e2#32)
  | .p144 => (144, 0xa9012402#32)
  | .p148 => (148, 0x52800029#32)
  | .p152 => (152, 0xd10043ff#32)
  | .p156 => (156, 0xf90003ea#32)
  | .p160 => (160, 0xf90007eb#32)
  | .p164 => (164, 0x9100000a#32)
  | .p168 => (168, 0xf9000149#32)
  | .p172 => (172, 0xd280000b#32)
  | .p176 => (176, 0xf900054b#32)
  | .p180 => (180, 0xf94007eb#32)
  | .p184 => (184, 0xf94003ea#32)
  | .p188 => (188, 0x910043ff#32)
  | .p192 => (192, 0xd65f03c0#32)
  | .p196 => (196, 0xd10043ff#32)
  | .p200 => (200, 0xf90003e9#32)
  | .p204 => (204, 0xf90007ea#32)
  | .p208 => (208, 0x91000009#32)
  | .p212 => (212, 0x91004129#32)
  | .p216 => (216, 0xf9000122#32)
  | .p220 => (220, 0xd280000a#32)
  | .p224 => (224, 0xf900052a#32)
  | .p228 => (228, 0xf94007ea#32)
  | .p232 => (232, 0xf94003e9#32)
  | .p236 => (236, 0x910043ff#32)
  | .p240 => (240, 0x52800029#32)
  | .p244 => (244, 0xd10043ff#32)
  | .p248 => (248, 0xf90003ea#32)
  | .p252 => (252, 0xf90007eb#32)
  | .p256 => (256, 0x9100000a#32)
  | .p260 => (260, 0xf9000149#32)
  | .p264 => (264, 0xd280000b#32)
  | .p268 => (268, 0xf900054b#32)
  | .p272 => (272, 0xf94007eb#32)
  | .p276 => (276, 0xf94003ea#32)
  | .p280 => (280, 0x910043ff#32)
  | .p284 => (284, 0xd65f03c0#32)
  | .p288 => (288, 0xaa0803e2#32)
  | .p292 => (292, 0xd10043ff#32)
  | .p296 => (296, 0xf90003e9#32)
  | .p300 => (300, 0xf90007ea#32)
  | .p304 => (304, 0x91000009#32)
  | .p308 => (308, 0x91004129#32)
  | .p312 => (312, 0xf9000122#32)
  | .p316 => (316, 0xd280000a#32)
  | .p320 => (320, 0xf900052a#32)
  | .p324 => (324, 0xf94007ea#32)
  | .p328 => (328, 0xf94003e9#32)
  | .p332 => (332, 0x910043ff#32)
  | .p336 => (336, 0x52800029#32)
  | .p340 => (340, 0xd10043ff#32)
  | .p344 => (344, 0xf90003ea#32)
  | .p348 => (348, 0xf90007eb#32)
  | .p352 => (352, 0x9100000a#32)
  | .p356 => (356, 0xf9000149#32)
  | .p360 => (360, 0xd280000b#32)
  | .p364 => (364, 0xf900054b#32)
  | .p368 => (368, 0xf94007eb#32)
  | .p372 => (372, 0xf94003ea#32)
  | .p376 => (376, 0x910043ff#32)
  | .p380 => (380, 0xd65f03c0#32)

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

def Op.effect (base : BitVec 64) : Op → ArmState → ArmState
  | .p0, s => w .PC (if (r (.GPR 1#5) s) = 0#64 then base + 196#64 else base + 4#64) s
  | .p4, s => put 9 ((r (.GPR 2#5) s) - 1#64) s
  | .p8, s => write_pstate (AddWithCarry (r (.GPR 9#5) s) 1#64 0#1).2 (next s)
  | .p12, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 120#64 else base + 16#64) s
  | .p16, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p20, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 11#5) s) s)
  | .p24, s => put 11 (r (.GPR 9#5) s) s
  | .p28, s => put 11 ((r (.GPR 11#5) s) <<< 3) s
  | .p32, s => put 11 ((r (.GPR 1#5) s) + (r (.GPR 11#5) s)) s
  | .p36, s => put 10 (read_mem_bytes 8 (r (.GPR 11#5) s) s) s
  | .p40, s => put 11 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p44, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p48, s => put 8 (r (.GPR 9#5) s) s
  | .p52, s => put 9 ((r (.GPR 9#5) s) - 1#64) s
  | .p56, s => w .PC (if (r (.GPR 10#5) s) = 0#64 then base + 8#64 else base + 60#64) s
  | .p60, s => put 8 ((r (.GPR 8#5) s) + 1#64) s
  | .p64, s => Udivti3.compare (r (.GPR 8#5) s) 3#64 s
  | .p68, s => w .PC (if r (.FLAG .C) s ≠ 1#1 then base + 124#64 else base + 72#64) s
  | .p72, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p76, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p80, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p84, s => put 9 ((r (.GPR 0#5) s) + 0#64) s
  | .p88, s => put 10 0#64 s
  | .p92, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p96, s => put 10 0#64 s
  | .p100, s => next (write_mem_bytes 8 ((r (.GPR 9#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p104, s => put 10 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p108, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p112, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p116, s => w .PC (r (.GPR 30#5) s) s
  | .p120, s => w .PC (if (r (.GPR 2#5) s) = 0#64 then base + 196#64 else base + 124#64) s
  | .p124, s => put 8 (read_mem_bytes 8 (r (.GPR 1#5) s) s) s
  | .p128, s => Udivti3.compare (r (.GPR 2#5) s) 2#64 s
  | .p132, s => w .PC (if r (.FLAG .C) s ≠ 1#1 then base + 288#64 else base + 136#64) s
  | .p136, s => put 9 (read_mem_bytes 8 ((r (.GPR 1#5) s) + 8#64) s) s
  | .p140, s => put 2 (r (.GPR 8#5) s) s
  | .p144, s => next (write_mem_bytes 16 ((r (.GPR 0#5) s) + 16#64) ((r (.GPR 9#5) s) ++ (r (.GPR 2#5) s)) s)
  | .p148, s => put 9 1#64 s
  | .p152, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p156, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 10#5) s) s)
  | .p160, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 11#5) s) s)
  | .p164, s => put 10 ((r (.GPR 0#5) s) + 0#64) s
  | .p168, s => next (write_mem_bytes 8 (r (.GPR 10#5) s) (r (.GPR 9#5) s) s)
  | .p172, s => put 11 0#64 s
  | .p176, s => next (write_mem_bytes 8 ((r (.GPR 10#5) s) + 8#64) (r (.GPR 11#5) s) s)
  | .p180, s => put 11 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p184, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p188, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p192, s => w .PC (r (.GPR 30#5) s) s
  | .p196, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p200, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p204, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p208, s => put 9 ((r (.GPR 0#5) s) + 0#64) s
  | .p212, s => put 9 ((r (.GPR 9#5) s) + 16#64) s
  | .p216, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 2#5) s) s)
  | .p220, s => put 10 0#64 s
  | .p224, s => next (write_mem_bytes 8 ((r (.GPR 9#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p228, s => put 10 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p232, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p236, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p240, s => put 9 1#64 s
  | .p244, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p248, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 10#5) s) s)
  | .p252, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 11#5) s) s)
  | .p256, s => put 10 ((r (.GPR 0#5) s) + 0#64) s
  | .p260, s => next (write_mem_bytes 8 (r (.GPR 10#5) s) (r (.GPR 9#5) s) s)
  | .p264, s => put 11 0#64 s
  | .p268, s => next (write_mem_bytes 8 ((r (.GPR 10#5) s) + 8#64) (r (.GPR 11#5) s) s)
  | .p272, s => put 11 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p276, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p280, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p284, s => w .PC (r (.GPR 30#5) s) s
  | .p288, s => put 2 (r (.GPR 8#5) s) s
  | .p292, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p296, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p300, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p304, s => put 9 ((r (.GPR 0#5) s) + 0#64) s
  | .p308, s => put 9 ((r (.GPR 9#5) s) + 16#64) s
  | .p312, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 2#5) s) s)
  | .p316, s => put 10 0#64 s
  | .p320, s => next (write_mem_bytes 8 ((r (.GPR 9#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p324, s => put 10 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p328, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p332, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p336, s => put 9 1#64 s
  | .p340, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p344, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 10#5) s) s)
  | .p348, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 11#5) s) s)
  | .p352, s => put 10 ((r (.GPR 0#5) s) + 0#64) s
  | .p356, s => next (write_mem_bytes 8 (r (.GPR 10#5) s) (r (.GPR 9#5) s) s)
  | .p360, s => put 11 0#64 s
  | .p364, s => next (write_mem_bytes 8 ((r (.GPR 10#5) s) + 8#64) (r (.GPR 11#5) s) s)
  | .p368, s => put 11 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p372, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p376, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p380, s => w .PC (r (.GPR 30#5) s) s

/-- Each concrete effect is proved against the actual fetched machine word. -/
theorem step (s : ArmState) (base : BitVec 64) (op : Op)
    (hc : CodeAt s base) (hp : read_pc s = base + BitVec.ofNat 64 op.row.1)
    (he : read_err s = .None) (ha : CheckSPAlignment s) : stepi s = op.effect base s := by
  have hm : op.row ∈ program := by cases op <;> decide
  have hf := hc op.row hm
  have hz : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by bv_omega
  cases op
  all_goals
    simp only [Op.row] at hp hf
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
      (fetch_inst_from_program.trans hf) rfl]
    change r .PC s = _ at hp
    simp (config := {decide := true, instances := true})
      [Op.effect, put, next, Udivti3.compare, Udivti3.next,
       exec_inst, state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
       BitVec.sub_eq_add_neg, ha, hp, BitVec.add_assoc, apply_ite, uint_lsl3_mask,
       uint_and_ones, hz]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all)
    | simp [w, write_base_pc, write_base_gpr]

@[simp] theorem Op.program (op : Op) (base : BitVec 64) (s : ArmState) :
    (op.effect base s).program = s.program := by
  cases op <;> simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]

@[simp] theorem Op.error (op : Op) (base : BitVec 64) (s : ArmState) :
    read_err (op.effect base s) = read_err s := by
  cases op <;> simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]

theorem Op.aligned (op : Op) (base : BitVec 64) (s : ArmState)
    (ha : CheckSPAlignment s) : CheckSPAlignment (op.effect base s) := by
  cases op <;> simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules, ha]
  all_goals first
    | exact BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s ha)
    | exact BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s ha)

@[simp] theorem Op.sfp (op : Op) (base : BitVec 64) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (op.effect base s) = r (.SFP reg) s := by
  cases op <;> simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]

def block (base : BitVec 64) (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect base t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      Follows base ops (op.effect base s)

theorem block_run (base : BitVec 64) (ops : List Op) (s : ArmState)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : Follows base ops s) : run ops.length s = block base ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = block base ops (op.effect base s)
    rw [run, step s base op hc hf.1 he ha]
    exact ih _ (by simpa only [CodeAt, Op.program] using hc)
      (by simpa only [Op.error] using he) (op.aligned base s ha) hf.2

end SszArm.NatToU128

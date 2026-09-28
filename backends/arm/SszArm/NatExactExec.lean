import SszArm.NatExactImpl
import SszArm.NatCompareExec

namespace SszArm.NatExact

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
  | p288 | p292
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p0 => (0, 0xa9402029#32)
  | .p4 => (4, 0xb4000369#32)
  | .p8 => (8, 0xd100050b#32)
  | .p12 => (12, 0xb100057f#32)
  | .p16 => (16, 0x54000200#32)
  | .p20 => (20, 0xd10043ff#32)
  | .p24 => (24, 0xf90003ea#32)
  | .p28 => (28, 0xaa0b03ea#32)
  | .p32 => (32, 0xd37df14a#32)
  | .p36 => (36, 0x8b0a012a#32)
  | .p40 => (40, 0xf940014c#32)
  | .p44 => (44, 0xf94003ea#32)
  | .p48 => (48, 0x910043ff#32)
  | .p52 => (52, 0xaa0b03ea#32)
  | .p56 => (56, 0xd100056b#32)
  | .p60 => (60, 0xb4fffe8c#32)
  | .p64 => (64, 0x9100054a#32)
  | .p68 => (68, 0xf1000d5f#32)
  | .p72 => (72, 0x54000063#32)
  | .p76 => (76, 0x1400000c#32)
  | .p80 => (80, 0xb4000648#32)
  | .p84 => (84, 0xf940012a#32)
  | .p88 => (88, 0xf100091f#32)
  | .p92 => (92, 0x54000063#32)
  | .p96 => (96, 0xf9400529#32)
  | .p100 => (100, 0x14000002#32)
  | .p104 => (104, 0xaa1f03e9#32)
  | .p108 => (108, 0xaa0a03e8#32)
  | .p112 => (112, 0xca020108#32)
  | .p116 => (116, 0xaa090108#32)
  | .p120 => (120, 0xb40004c8#32)
  | .p124 => (124, 0x52800028#32)
  | .p128 => (128, 0xd10043ff#32)
  | .p132 => (132, 0xf90003e9#32)
  | .p136 => (136, 0xf90007ea#32)
  | .p140 => (140, 0x91000009#32)
  | .p144 => (144, 0x91008129#32)
  | .p148 => (148, 0xd280000a#32)
  | .p152 => (152, 0xf900012a#32)
  | .p156 => (156, 0xf9000522#32)
  | .p160 => (160, 0xf94007ea#32)
  | .p164 => (164, 0xf94003e9#32)
  | .p168 => (168, 0x910043ff#32)
  | .p172 => (172, 0xd10043ff#32)
  | .p176 => (176, 0xf90003e9#32)
  | .p180 => (180, 0xf90007ea#32)
  | .p184 => (184, 0x91000009#32)
  | .p188 => (188, 0xf9000128#32)
  | .p192 => (192, 0xd280000a#32)
  | .p196 => (196, 0xf900052a#32)
  | .p200 => (200, 0xf94007ea#32)
  | .p204 => (204, 0xf94003e9#32)
  | .p208 => (208, 0x910043ff#32)
  | .p212 => (212, 0xa9402428#32)
  | .p216 => (216, 0xd10043ff#32)
  | .p220 => (220, 0xf90003e9#32)
  | .p224 => (224, 0xf90007ea#32)
  | .p228 => (228, 0x91000009#32)
  | .p232 => (232, 0x9100c129#32)
  | .p236 => (236, 0xd280000a#32)
  | .p240 => (240, 0xf900012a#32)
  | .p244 => (244, 0xd280000a#32)
  | .p248 => (248, 0xf900052a#32)
  | .p252 => (252, 0xf94007ea#32)
  | .p256 => (256, 0xf94003e9#32)
  | .p260 => (260, 0x910043ff#32)
  | .p264 => (264, 0xa9012408#32)
  | .p268 => (268, 0x52800068#32)
  | .p272 => (272, 0xb9004008#32)
  | .p276 => (276, 0xd65f03c0#32)
  | .p280 => (280, 0xca020108#32)
  | .p284 => (284, 0xaa1f0108#32)
  | .p288 => (288, 0xb5fffae8#32)
  | .p292 => (292, 0x17fffffb#32)

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

def Op.effect (base : BitVec 64) : Op → ArmState → ArmState
  | .p0, s => next (w (.GPR 8#5) (read_mem_bytes 8 ((r (.GPR 1#5) s) + 8#64) s) (w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 1#5) s) s) s))
  | .p4, s => w .PC (if (r (.GPR 9#5) s) = 0#64 then base + 112#64 else base + 8#64) s
  | .p8, s => put 11 ((r (.GPR 8#5) s) - 1#64) s
  | .p12, s => write_pstate (AddWithCarry (r (.GPR 11#5) s) 1#64 0#1).2 (next s)
  | .p16, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 80#64 else base + 20#64) s
  | .p20, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p24, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 10#5) s) s)
  | .p28, s => put 10 (r (.GPR 11#5) s) s
  | .p32, s => put 10 ((r (.GPR 10#5) s) <<< 3) s
  | .p36, s => put 10 ((r (.GPR 9#5) s) + (r (.GPR 10#5) s)) s
  | .p40, s => put 12 (read_mem_bytes 8 (r (.GPR 10#5) s) s) s
  | .p44, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p48, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p52, s => put 10 (r (.GPR 11#5) s) s
  | .p56, s => put 11 ((r (.GPR 11#5) s) - 1#64) s
  | .p60, s => w .PC (if (r (.GPR 12#5) s) = 0#64 then base + 12#64 else base + 64#64) s
  | .p64, s => put 10 ((r (.GPR 10#5) s) + 1#64) s
  | .p68, s => Udivti3.compare (r (.GPR 10#5) s) 3#64 s
  | .p72, s => w .PC (if r (.FLAG .C) s ≠ 1#1 then base + 84#64 else base + 76#64) s
  | .p76, s => w .PC (base + 124#64) s
  | .p80, s => w .PC (if (r (.GPR 8#5) s) = 0#64 then base + 280#64 else base + 84#64) s
  | .p84, s => put 10 (read_mem_bytes 8 (r (.GPR 9#5) s) s) s
  | .p88, s => Udivti3.compare (r (.GPR 8#5) s) 2#64 s
  | .p92, s => w .PC (if r (.FLAG .C) s ≠ 1#1 then base + 104#64 else base + 96#64) s
  | .p96, s => put 9 (read_mem_bytes 8 ((r (.GPR 9#5) s) + 8#64) s) s
  | .p100, s => w .PC (base + 108#64) s
  | .p104, s => put 9 0#64 s
  | .p108, s => put 8 (r (.GPR 10#5) s) s
  | .p112, s => put 8 ((r (.GPR 8#5) s) ^^^ (r (.GPR 2#5) s)) s
  | .p116, s => put 8 ((r (.GPR 8#5) s) ||| (r (.GPR 9#5) s)) s
  | .p120, s => w .PC (if (r (.GPR 8#5) s) = 0#64 then base + 272#64 else base + 124#64) s
  | .p124, s => put 8 1#64 s
  | .p128, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p132, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p136, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p140, s => put 9 ((r (.GPR 0#5) s) + 0#64) s
  | .p144, s => put 9 ((r (.GPR 9#5) s) + 32#64) s
  | .p148, s => put 10 0#64 s
  | .p152, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p156, s => next (write_mem_bytes 8 ((r (.GPR 9#5) s) + 8#64) (r (.GPR 2#5) s) s)
  | .p160, s => put 10 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p164, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p168, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p172, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p176, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p180, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p184, s => put 9 ((r (.GPR 0#5) s) + 0#64) s
  | .p188, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 8#5) s) s)
  | .p192, s => put 10 0#64 s
  | .p196, s => next (write_mem_bytes 8 ((r (.GPR 9#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p200, s => put 10 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p204, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p208, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p212, s => next (w (.GPR 9#5) (read_mem_bytes 8 ((r (.GPR 1#5) s) + 8#64) s) (w (.GPR 8#5) (read_mem_bytes 8 (r (.GPR 1#5) s) s) s))
  | .p216, s => put 31 ((r (.GPR 31#5) s) - 16#64) s
  | .p220, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p224, s => next (write_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p228, s => put 9 ((r (.GPR 0#5) s) + 0#64) s
  | .p232, s => put 9 ((r (.GPR 9#5) s) + 48#64) s
  | .p236, s => put 10 0#64 s
  | .p240, s => next (write_mem_bytes 8 (r (.GPR 9#5) s) (r (.GPR 10#5) s) s)
  | .p244, s => put 10 0#64 s
  | .p248, s => next (write_mem_bytes 8 ((r (.GPR 9#5) s) + 8#64) (r (.GPR 10#5) s) s)
  | .p252, s => put 10 (read_mem_bytes 8 ((r (.GPR 31#5) s) + 8#64) s) s
  | .p256, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p260, s => put 31 ((r (.GPR 31#5) s) + 16#64) s
  | .p264, s => next (write_mem_bytes 16 ((r (.GPR 0#5) s) + 16#64) ((r (.GPR 9#5) s) ++ (r (.GPR 8#5) s)) s)
  | .p268, s => put 8 3#64 s
  | .p272, s => next (write_mem_bytes 4 ((r (.GPR 0#5) s) + 64#64) ((r (.GPR 8#5) s).setWidth 32) s)
  | .p276, s => w .PC (r (.GPR 30#5) s) s
  | .p280, s => put 8 ((r (.GPR 8#5) s) ^^^ (r (.GPR 2#5) s)) s
  | .p284, s => put 8 ((r (.GPR 8#5) s) ||| 0#64) s
  | .p288, s => w .PC (if (r (.GPR 8#5) s) ≠ 0#64 then base + 124#64 else base + 292#64) s
  | .p292, s => w .PC (base + 272#64) s

/-- Each concrete effect is proved against the actual fetched machine word. -/
theorem step (s : ArmState) (base : BitVec 64) (op : Op)
    (hc : CodeAt s base) (hp : read_pc s = base + BitVec.ofNat 64 op.row.1)
    (he : read_err s = .None) (ha : CheckSPAlignment s) : stepi s = op.effect base s := by
  have hm : op.row ∈ program := by cases op <;> decide
  have hf := hc op.row hm
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
       uint_and_ones, BoolCodec.pair_read_low, BoolCodec.pair_read_high]
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

end SszArm.NatExact

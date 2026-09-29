import SszArm.IndicesLinkedIsPowerOfTwo
import SszArm.NatToU128Memory

namespace SszArm.Indices.IsPowerOfTwo

open UintCodec

abbrev CodeAt := Linked.IsPowerOfTwo.CodeAt

inductive Op where
  | p0 | p4 | p8 | p12 | p16 | p20 | p24 | p28 | p32 | p36 | p40 | p44
  | p48 | p52 | p56 | p60 | p64 | p68 | p72 | p76 | p80 | p84 | p88 | p92
  | p96 | p100 | p104 | p108 | p112 | p116 | p120 | p124 | p128 | p132
  | p136 | p140 | p144 | p148 | p152 | p156 | p160 | p164 | p168 | p172
  | p176 | p180 | p184 | p188 | p192 | p196 | p200 | p204 | p208 | p212
  | p216 | p220 | p224 | p228 | p232 | p236 | p240 | p244
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p0 => (0, 0xb40006a0#32)
  | .p4 => (4, 0xd1002008#32)
  | .p8 => (8, 0xaa0103e9#32)
  | .p12 => (12, 0xb4000609#32)
  | .p16 => (16, 0xd10043ff#32)
  | .p20 => (20, 0xf90003ea#32)
  | .p24 => (24, 0xaa0903ea#32)
  | .p28 => (28, 0xd37df14a#32)
  | .p32 => (32, 0x8b0a010a#32)
  | .p36 => (36, 0xf940014b#32)
  | .p40 => (40, 0xf94003ea#32)
  | .p44 => (44, 0x910043ff#32)
  | .p48 => (48, 0xd100052a#32)
  | .p52 => (52, 0xaa0a03e9#32)
  | .p56 => (56, 0xb4fffeab#32)
  | .p60 => (60, 0x2a1f03e8#32)
  | .p64 => (64, 0xaa1f03e9#32)
  | .p68 => (68, 0x9100054a#32)
  | .p72 => (72, 0x14000005#32)
  | .p76 => (76, 0x52800028#32)
  | .p80 => (80, 0x91000529#32)
  | .p84 => (84, 0xeb09015f#32)
  | .p88 => (88, 0x540004c0#32)
  | .p92 => (92, 0xeb01013f#32)
  | .p96 => (96, 0x54ffff82#32)
  | .p100 => (100, 0xd10043ff#32)
  | .p104 => (104, 0xf90003ea#32)
  | .p108 => (108, 0xaa0903ea#32)
  | .p112 => (112, 0xd37df14a#32)
  | .p116 => (116, 0x8b0a000a#32)
  | .p120 => (120, 0xf940014b#32)
  | .p124 => (124, 0xf94003ea#32)
  | .p128 => (128, 0x910043ff#32)
  | .p132 => (132, 0xb4fffe6b#32)
  | .p136 => (136, 0xd100056c#32)
  | .p140 => (140, 0xea0c017f#32)
  | .p144 => (144, 0x54000061#32)
  | .p148 => (148, 0x5280000b#32)
  | .p152 => (152, 0x14000002#32)
  | .p156 => (156, 0x5280002b#32)
  | .p160 => (160, 0x2a0b0108#32)
  | .p164 => (164, 0xd10043ff#32)
  | .p168 => (168, 0xf90003e9#32)
  | .p172 => (172, 0x12000109#32)
  | .p176 => (176, 0x34000089#32)
  | .p180 => (180, 0xf94003e9#32)
  | .p184 => (184, 0x910043ff#32)
  | .p188 => (188, 0x14000004#32)
  | .p192 => (192, 0xf94003e9#32)
  | .p196 => (196, 0x910043ff#32)
  | .p200 => (200, 0x17ffffe1#32)
  | .p204 => (204, 0x120003e0#32)
  | .p208 => (208, 0xd65f03c0#32)
  | .p212 => (212, 0xd1000428#32)
  | .p216 => (216, 0xca080029#32)
  | .p220 => (220, 0xeb08013f#32)
  | .p224 => (224, 0x54000068#32)
  | .p228 => (228, 0x52800008#32)
  | .p232 => (232, 0x14000002#32)
  | .p236 => (236, 0x52800028#32)
  | .p240 => (240, 0x12000100#32)
  | .p244 => (244, 0xd65f03c0#32)

abbrev next := NatCompare.next
abbrev put := NatCompare.put

def test (a b : BitVec 64) (s : ArmState) : ArmState :=
  let value := a &&& b
  write_pstate ⟨value.msb.toBitVec, (value == 0).toBitVec, 0#1, 0#1⟩ (next s)

def Op.effect (base : BitVec 64) : Op → ArmState → ArmState
  | .p0, s => w .PC (if r (.GPR 0#5) s = 0 then base + 212 else base + 4) s
  | .p4, s => put 8 (r (.GPR 0#5) s - 8) s
  | .p8, s => put 9 (r (.GPR 1#5) s) s
  | .p12, s => w .PC (if r (.GPR 9#5) s = 0 then base + 204 else base + 16) s
  | .p16, s => put 31 (r (.GPR 31#5) s - 16) s
  | .p20, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 10#5) s) s)
  | .p24, s => put 10 (r (.GPR 9#5) s) s
  | .p28, s => put 10 (r (.GPR 10#5) s <<< 3) s
  | .p32, s => put 10 (r (.GPR 8#5) s + r (.GPR 10#5) s) s
  | .p36, s => put 11 (read_mem_bytes 8 (r (.GPR 10#5) s) s) s
  | .p40, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p44, s => put 31 (r (.GPR 31#5) s + 16) s
  | .p48, s => put 10 (r (.GPR 9#5) s - 1) s
  | .p52, s => put 9 (r (.GPR 10#5) s) s
  | .p56, s => w .PC (if r (.GPR 11#5) s = 0 then base + 12 else base + 60) s
  | .p60, s => put 8 0 s
  | .p64, s => put 9 0 s
  | .p68, s => put 10 (r (.GPR 10#5) s + 1) s
  | .p72, s => w .PC (base + 92) s
  | .p76, s => put 8 1 s
  | .p80, s => put 9 (r (.GPR 9#5) s + 1) s
  | .p84, s => Udivti3.compare (r (.GPR 10#5) s) (r (.GPR 9#5) s) s
  | .p88, s => w .PC (if r (.FLAG .Z) s = 1 then base + 240 else base + 92) s
  | .p92, s => Udivti3.compare (r (.GPR 9#5) s) (r (.GPR 1#5) s) s
  | .p96, s => w .PC (if r (.FLAG .C) s = 1 then base + 80 else base + 100) s
  | .p100, s => put 31 (r (.GPR 31#5) s - 16) s
  | .p104, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 10#5) s) s)
  | .p108, s => put 10 (r (.GPR 9#5) s) s
  | .p112, s => put 10 (r (.GPR 10#5) s <<< 3) s
  | .p116, s => put 10 (r (.GPR 0#5) s + r (.GPR 10#5) s) s
  | .p120, s => put 11 (read_mem_bytes 8 (r (.GPR 10#5) s) s) s
  | .p124, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p128, s => put 31 (r (.GPR 31#5) s + 16) s
  | .p132, s => w .PC (if r (.GPR 11#5) s = 0 then base + 80 else base + 136) s
  | .p136, s => put 12 (r (.GPR 11#5) s - 1) s
  | .p140, s => test (r (.GPR 11#5) s) (r (.GPR 12#5) s) s
  | .p144, s => w .PC (if r (.FLAG .Z) s = 1 then base + 148 else base + 156) s
  | .p148, s => put 11 0 s
  | .p152, s => w .PC (base + 160) s
  | .p156, s => put 11 1 s
  | .p160, s => put 8 (((r (.GPR 8#5) s ||| r (.GPR 11#5) s).setWidth 32).setWidth 64) s
  | .p164, s => put 31 (r (.GPR 31#5) s - 16) s
  | .p168, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p172, s => put 9 (r (.GPR 8#5) s &&& 1) s
  | .p176, s => w .PC (if (r (.GPR 9#5) s).setWidth 32 = 0 then base + 192 else base + 180) s
  | .p180, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p184, s => put 31 (r (.GPR 31#5) s + 16) s
  | .p188, s => w .PC (base + 204) s
  | .p192, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p196, s => put 31 (r (.GPR 31#5) s + 16) s
  | .p200, s => w .PC (base + 76) s
  | .p204, s => put 0 0 s
  | .p208, s => w .PC (r (.GPR 30#5) s) s
  | .p212, s => put 8 (r (.GPR 1#5) s - 1) s
  | .p216, s => put 9 (r (.GPR 1#5) s ^^^ r (.GPR 8#5) s) s
  | .p220, s => Udivti3.compare (r (.GPR 9#5) s) (r (.GPR 8#5) s) s
  | .p224, s => w .PC (if r (.FLAG .C) s = 1 ∧ r (.FLAG .Z) s = 0 then base + 236 else base + 228) s
  | .p228, s => put 8 0 s
  | .p232, s => w .PC (base + 240) s
  | .p236, s => put 8 1 s
  | .p240, s => put 0 (r (.GPR 8#5) s &&& 1) s
  | .p244, s => w .PC (r (.GPR 30#5) s) s

theorem step (s : ArmState) (base : BitVec 64) (op : Op)
    (code : CodeAt s base) (pc : read_pc s = base + BitVec.ofNat 64 op.row.1)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) :
    stepi s = op.effect base s := by
  have fetched := code op.row (by cases op <;> decide)
  have zero : (r (.FLAG .Z) s ≠ 0#1) ↔ r (.FLAG .Z) s = 1#1 := by
    have bound := (r (.FLAG .Z) s).isLt
    constructor <;> intro h <;> apply BitVec.eq_of_toNat_eq <;>
      simp_all only [BitVec.toNat_eq, BitVec.toNat_ofNat] <;> omega
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    change r .PC s = _ at pc
    simp (config := {decide := true, instances := true})
      [Op.effect, put, next, NatCompare.put, NatCompare.next, test,
       Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
       bitvec_rules, minimal_theory, BitVec.setWidth_eq,
       BitVec.sub_eq_add_neg, aligned, pc, BitVec.add_assoc, apply_ite,
       uint_lsl3_mask, uint_and_ones, zero]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all)
    | simp [w, write_base_pc, write_base_gpr]

@[simp] theorem Op.program (op : Op) (base : BitVec 64) (s : ArmState) :
    (op.effect base s).program = s.program := by
  cases op <;> simp [Op.effect, put, next, NatCompare.put, NatCompare.next,
    test, Udivti3.compare, Udivti3.next, state_simp_rules]

@[simp] theorem Op.error (op : Op) (base : BitVec 64) (s : ArmState) :
    read_err (op.effect base s) = read_err s := by
  cases op <;> simp [Op.effect, put, next, NatCompare.put, NatCompare.next,
    test, Udivti3.compare, Udivti3.next, state_simp_rules]

@[simp] theorem Op.sfp (op : Op) (base : BitVec 64) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (op.effect base s) = r (.SFP reg) s := by
  cases op <;> simp [Op.effect, put, next, NatCompare.put, NatCompare.next,
    test, Udivti3.compare, Udivti3.next, state_simp_rules]

theorem Op.aligned (op : Op) (base : BitVec 64) (s : ArmState)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (op.effect base s) := by
  cases op <;> simp [Op.effect, put, next, NatCompare.put, NatCompare.next,
    test, Udivti3.compare, Udivti3.next, state_simp_rules, aligned]
  all_goals first
    | exact BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s aligned)
    | exact BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s aligned)

def block (base : BitVec 64) (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect base t) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      Follows base ops (op.effect base s)

theorem block_run (base : BitVec 64) (ops : List Op) (s : ArmState)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (follows : Follows base ops s) : run ops.length s = block base ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = block base ops (op.effect base s)
    rw [run, step s base op code follows.1 error aligned]
    exact ih _ (by simpa only [CodeAt, Linked.IsPowerOfTwo.CodeAt,
      Codec.Linked.WordsAt, Op.program] using code)
      (by simpa only [Op.error] using error) (op.aligned base s aligned) follows.2

end SszArm.Indices.IsPowerOfTwo

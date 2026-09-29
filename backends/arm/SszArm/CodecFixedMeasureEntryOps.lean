import SszArm.CodecFixedOps
import SszArm.CodecLinkedMeasureFixed

namespace SszArm.Codec.Fixed.MeasureFixed.Entry

open Dispatch.Block (next put save branch greater)
open IsFixed (loadPair)

inductive Op where
  | p0 | p4 | p8 | p12 | p16 | p20 | p24 | p28 | p32 | p36 | p40 | p44 | p48 | p52 | p56 | p60 | p64
  | p144 | p148 | p152 | p156 | p160 | p164 | p168 | p172 | p176 | p180 | p184
  | p188 | p192 | p196 | p200 | p204 | p208 | p212 | p216 | p220 | p224
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p0 => (0, 0xd10283ff#32)
  | .p4 => (4, 0xf9002bfe#32)
  | .p8 => (8, 0xa90667fa#32)
  | .p12 => (12, 0xa9075ff8#32)
  | .p16 => (16, 0xa90857f6#32)
  | .p20 => (20, 0xa9094ff4#32)
  | .p24 => (24, 0xf9400028#32)
  | .p28 => (28, 0xaa0003f3#32)
  | .p32 => (32, 0xf1000d1f#32)
  | .p36 => (36, 0x5400036d#32)
  | .p40 => (40, 0xaa0203f4#32)
  | .p44 => (44, 0xf100251f#32)
  | .p48 => (48, 0x540003ec#32)
  | .p52 => (52, 0xf100111f#32)
  | .p56 => (56, 0x54000560#32)
  | .p60 => (60, 0xf1001d1f#32)
  | .p64 => (64, 0x54001201#32)
  | .p144 => (144, 0xb4000248#32)
  | .p148 => (148, 0xf100051f#32)
  | .p152 => (152, 0x54000060#32)
  | .p156 => (156, 0xf100091f#32)
  | .p160 => (160, 0x54000f01#32)
  | .p164 => (164, 0xa940d835#32)
  | .p168 => (168, 0x14000072#32)
  | .p172 => (172, 0xf100291f#32)
  | .p176 => (176, 0x54000420#32)
  | .p180 => (180, 0xf1002d1f#32)
  | .p184 => (184, 0x54000e41#32)
  | .p188 => (188, 0x52800308#32)
  | .p192 => (192, 0x8b080028#32)
  | .p196 => (196, 0xf9400509#32)
  | .p200 => (200, 0xb50003e9#32)
  | .p204 => (204, 0xaa1f03f5#32)
  | .p208 => (208, 0xaa1f03f6#32)
  | .p212 => (212, 0x14000067#32)
  | .p216 => (216, 0xaa1f03f5#32)
  | .p220 => (220, 0x52800036#32)
  | .p224 => (224, 0x14000064#32)

def Op.effect : Op → ArmState → ArmState
  | .p0, s => put 31 (r (.GPR 31#5) s - 160#64) s
  | .p4, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 80#64) (r (.GPR 30#5) s) s)
  | .p8, s => save 26 25 96#64 s
  | .p12, s => save 24 23 112#64 s
  | .p16, s => save 22 21 128#64 s
  | .p20, s => save 20 19 144#64 s
  | .p24, s => put 8 (read_mem_bytes 8 (r (.GPR 1#5) s) s) s
  | .p28, s => put 19 (r (.GPR 0#5) s) s
  | .p32, s => Udivti3.compare (r (.GPR 8#5) s) 3#64 s
  | .p36, s => branch (¬ greater s) 108#64 s
  | .p40, s => put 20 (r (.GPR 2#5) s) s
  | .p44, s => Udivti3.compare (r (.GPR 8#5) s) 9#64 s
  | .p48, s => branch (greater s) 124#64 s
  | .p52, s => Udivti3.compare (r (.GPR 8#5) s) 4#64 s
  | .p56, s => branch (r (.FLAG .Z) s = 1#1) 172#64 s
  | .p60, s => Udivti3.compare (r (.GPR 8#5) s) 7#64 s
  | .p64, s => branch (r (.FLAG .Z) s ≠ 1#1) 576#64 s
  | .p144, s => branch (r (.GPR 8#5) s = 0#64) 72#64 s
  | .p148, s => Udivti3.compare (r (.GPR 8#5) s) 1#64 s
  | .p152, s => branch (r (.FLAG .Z) s = 1#1) 12#64 s
  | .p156, s => Udivti3.compare (r (.GPR 8#5) s) 2#64 s
  | .p160, s => branch (r (.FLAG .Z) s ≠ 1#1) 480#64 s
  | .p164, s => loadPair 21 22 1 8#64 s
  | .p168, s => w .PC (read_pc s + 456#64) s
  | .p172, s => Udivti3.compare (r (.GPR 8#5) s) 10#64 s
  | .p176, s => branch (r (.FLAG .Z) s = 1#1) 132#64 s
  | .p180, s => Udivti3.compare (r (.GPR 8#5) s) 11#64 s
  | .p184, s => branch (r (.FLAG .Z) s ≠ 1#1) 456#64 s
  | .p188, s => put 8 24#64 s
  | .p192, s => put 8 (r (.GPR 1#5) s + r (.GPR 8#5) s) s
  | .p196, s => put 9 (read_mem_bytes 8 (r (.GPR 8#5) s + 8#64) s) s
  | .p200, s => branch (r (.GPR 9#5) s ≠ 0#64) 124#64 s
  | .p204, s | .p216, s => put 21 0#64 s
  | .p208, s => put 22 0#64 s
  | .p212, s => w .PC (read_pc s + 412#64) s
  | .p220, s => put 22 1#64 s
  | .p224, s => w .PC (read_pc s + 400#64) s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.MeasureFixed.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) :
    stepi s = op.effect s := by
  have fetched := Linked.MeasureFixed.chunk0_codeAt code op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true}) [Op.effect, next, put, save, branch,
      greater, loadPair, Udivti3.compare, Udivti3.next, exec_inst, state_simp_rules,
      bitvec_rules, minimal_theory, aligned, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BoolCodec.pair_read_low, BoolCodec.pair_read_high, apply_ite]
  case p36 | p48 =>
    by_cases n : r (.FLAG .N) s = r (.FLAG .V) s <;>
      by_cases z : r (.FLAG .Z) s = 0#1 <;> simp_all
  all_goals first | rfl | exact w_of_w_commute (by decide) | (split <;> simp_all)

@[simp] theorem Op.program (op : Op) (s : ArmState) : (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, next, put, save, branch, loadPair,
    Udivti3.compare, Udivti3.next, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) : read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, next, put, save, branch, loadPair,
    Udivti3.compare, Udivti3.next, state_simp_rules]

@[simp] theorem Op.vector (op : Op) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (op.effect s) = r (.SFP reg) s := by
  cases op <;> simp [Op.effect, next, put, save, branch, loadPair,
    Udivti3.compare, Udivti3.next, state_simp_rules]

end SszArm.Codec.Fixed.MeasureFixed.Entry

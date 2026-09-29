import SszArm.DispatchBlocks

namespace SszArm.Codec.Fixed.IsFixed

inductive Op where
  | p0 | p4 | p8 | p12 | p16 | p20 | p24 | p28 | p32 | p36
  | p40 | p44 | p48 | p52 | p56 | p60 | p64 | p68 | p72 | p76
  | p80 | p84 | p88 | p92 | p96 | p100 | p104 | p108 | p112 | p116
  | p120 | p124 | p128 | p132 | p136 | p140 | p144 | p148 | p152 | p156
  | p160 | p164 | p168 | p172 | p176 | p180 | p184 | p188 | p192 | p196 | p200
  deriving DecidableEq

/-- The complete linked is_fixed extent, relative to its original entry. -/
def Op.row : Op → Nat × BitVec 32
  | .p0 => (0, 0xd10083ff#32)
  | .p4 => (4, 0xf90003fe#32)
  | .p8 => (8, 0xa9014ff4#32)
  | .p12 => (12, 0xf9400008#32)
  | .p16 => (16, 0xf1001d1f#32)
  | .p20 => (20, 0x540000a1#32)
  | .p24 => (24, 0xf9400c00#32)
  | .p28 => (28, 0xf9400008#32)
  | .p32 => (32, 0xf1001d1f#32)
  | .p36 => (36, 0x54ffffa0#32)
  | .p40 => (40, 0xf1000d1f#32)
  | .p44 => (44, 0x5400006c#32)
  | .p48 => (48, 0x54000463#32)
  | .p52 => (52, 0x1400001e#32)
  | .p56 => (56, 0xf100111f#32)
  | .p60 => (60, 0x54000400#32)
  | .p64 => (64, 0xf100291f#32)
  | .p68 => (68, 0x540000a0#32)
  | .p72 => (72, 0xf1002d1f#32)
  | .p76 => (76, 0x54000301#32)
  | .p80 => (80, 0x52800308#32)
  | .p84 => (84, 0x14000002#32)
  | .p88 => (88, 0x52800108#32)
  | .p92 => (92, 0x8b080008#32)
  | .p96 => (96, 0xa9402508#32)
  | .p100 => (100, 0x8b090529#32)
  | .p104 => (104, 0xd37df133#32)
  | .p108 => (108, 0xb4000293#32)
  | .p112 => (112, 0xf9400900#32)
  | .p116 => (116, 0x91006114#32)
  | .p120 => (120, 0x97ffffe2#32)
  | .p124 => (124, 0xd1006273#32)
  | .p128 => (128, 0xaa1403e8#32)
  | .p132 => (132, 0xd10043ff#32)
  | .p136 => (136, 0xf90003e9#32)
  | .p140 => (140, 0x12000009#32)
  | .p144 => (144, 0x35000089#32)
  | .p148 => (148, 0xf94003e9#32)
  | .p152 => (152, 0x910043ff#32)
  | .p156 => (156, 0x14000004#32)
  | .p160 => (160, 0xf94003e9#32)
  | .p164 => (164, 0x910043ff#32)
  | .p168 => (168, 0x17fffff1#32)
  | .p172 => (172, 0x2a1f03e0#32)
  | .p176 => (176, 0xa9414ff4#32)
  | .p180 => (180, 0xf84207fe#32)
  | .p184 => (184, 0xd65f03c0#32)
  | .p188 => (188, 0x52800020#32)
  | .p192 => (192, 0xa9414ff4#32)
  | .p196 => (196, 0xf84207fe#32)
  | .p200 => (200, 0xd65f03c0#32)

def CodeAt (s : ArmState) (base : BitVec 64) : Prop :=
  ∀ op : Op, s.program.find? (base + BitVec.ofNat 64 op.row.1) = some op.row.2

open Dispatch.Block (next put save branch greater)

def loadPair (first second address : BitVec 5) (offset : BitVec 64)
    (s : ArmState) : ArmState :=
  next (w (.GPR second) (read_mem_bytes 8 (r (.GPR address) s + offset + 8#64) s)
    (w (.GPR first) (read_mem_bytes 8 (r (.GPR address) s + offset) s) s))

def restore (s : ArmState) : ArmState :=
  next (w (.GPR 31#5) (r (.GPR 31#5) s + 32#64)
    (w (.GPR 30#5) (read_mem_bytes 8 (r (.GPR 31#5) s) s) s))

def Op.effect : Op → ArmState → ArmState
  | .p0, s => put 31 (r (.GPR 31#5) s - 32#64) s
  | .p4, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 30#5) s) s)
  | .p8, s => save 20 19 16#64 s
  | .p12, s | .p28, s => put 8 (read_mem_bytes 8 (r (.GPR 0#5) s) s) s
  | .p16, s | .p32, s => Udivti3.compare (r (.GPR 8#5) s) 7#64 s
  | .p20, s => branch (r (.FLAG .Z) s ≠ 1#1) 20#64 s
  | .p24, s => put 0 (read_mem_bytes 8 (r (.GPR 0#5) s + 24#64) s) s
  | .p36, s => branch (r (.FLAG .Z) s = 1#1) (-12#64) s
  | .p40, s => Udivti3.compare (r (.GPR 8#5) s) 3#64 s
  | .p44, s => branch (greater s) 12#64 s
  | .p48, s => branch (r (.FLAG .C) s = 0#1) 140#64 s
  | .p52, s => w .PC (read_pc s + 120#64) s
  | .p56, s => Udivti3.compare (r (.GPR 8#5) s) 4#64 s
  | .p60, s => branch (r (.FLAG .Z) s = 1#1) 128#64 s
  | .p64, s => Udivti3.compare (r (.GPR 8#5) s) 10#64 s
  | .p68, s => branch (r (.FLAG .Z) s = 1#1) 20#64 s
  | .p72, s => Udivti3.compare (r (.GPR 8#5) s) 11#64 s
  | .p76, s => branch (r (.FLAG .Z) s ≠ 1#1) 96#64 s
  | .p80, s => put 8 24#64 s
  | .p84, s => w .PC (read_pc s + 8#64) s
  | .p88, s => put 8 8#64 s
  | .p92, s => put 8 (r (.GPR 0#5) s + r (.GPR 8#5) s) s
  | .p96, s => loadPair 8 9 8 0#64 s
  | .p100, s => put 9 (r (.GPR 9#5) s + (r (.GPR 9#5) s <<< 1)) s
  | .p104, s => put 19 (r (.GPR 9#5) s <<< 3) s
  | .p108, s => branch (r (.GPR 19#5) s = 0#64) 80#64 s
  | .p112, s => put 0 (read_mem_bytes 8 (r (.GPR 8#5) s + 16#64) s) s
  | .p116, s => put 20 (r (.GPR 8#5) s + 24#64) s
  | .p120, s => w .PC (read_pc s - 120#64) (w (.GPR 30#5) (read_pc s + 4#64) s)
  | .p124, s => put 19 (r (.GPR 19#5) s - 24#64) s
  | .p128, s => put 8 (r (.GPR 20#5) s) s
  | .p132, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p136, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p140, s => put 9 (((r (.GPR 0#5) s).setWidth 32 &&& 1#32).setWidth 64) s
  | .p144, s => branch ((r (.GPR 9#5) s).setWidth 32 ≠ 0#32) 16#64 s
  | .p148, s | .p160, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p152, s | .p164, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p156, s => w .PC (read_pc s + 16#64) s
  | .p168, s => w .PC (read_pc s - 60#64) s
  | .p172, s => put 0 0#64 s
  | .p176, s | .p192, s => loadPair 20 19 31 16#64 s
  | .p180, s | .p196, s => restore s
  | .p184, s | .p200, s => w .PC (r (.GPR 30#5) s) s
  | .p188, s => put 0 1#64 s

@[simp] theorem Op.program (op : Op) (s : ArmState) : (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, next, put, save, branch, loadPair, restore,
    Udivti3.compare, Udivti3.next, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) : read_err (op.effect s) = read_err s := by
  cases op <;> simp [Op.effect, next, put, save, branch, loadPair, restore,
    Udivti3.compare, Udivti3.next, state_simp_rules]

@[simp] theorem Op.vector (op : Op) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (op.effect s) = r (.SFP reg) s := by
  cases op <;> simp [Op.effect, next, put, save, branch, loadPair, restore,
    Udivti3.compare, Udivti3.next, state_simp_rules]

end SszArm.Codec.Fixed.IsFixed

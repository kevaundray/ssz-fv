import SszArm.EmitDispatchOps
import SszArm.NatToU128Memory

namespace SszArm.Emit.Uint

inductive WidthOp where
  | p60 | p64 | p68 | p72 | p76 | p80 | p84 | p88 | p92 | p96
  | p100 | p104 | p108 | p112 | p116 | p120 | p124 | p128 | p132 | p136 | p140
  | p896 | p900 | p904 | p908 | p912
  deriving DecidableEq

def WidthOp.row : WidthOp → Nat × BitVec 32
  | .p60 => (60, 0x7100053f#32)
  | .p64 => (64, 0x540008e1#32)
  | .p68 => (68, 0xa9408428#32)
  | .p72 => (72, 0xb4001a08#32)
  | .p76 => (76, 0xd100042a#32)
  | .p80 => (80, 0xb100055f#32)
  | .p84 => (84, 0x54001960#32)
  | .p88 => (88, 0xd10043ff#32)
  | .p92 => (92, 0xf90003e9#32)
  | .p96 => (96, 0xaa0a03e9#32)
  | .p100 => (100, 0xd37df129#32)
  | .p104 => (104, 0x8b090109#32)
  | .p108 => (108, 0xf940012b#32)
  | .p112 => (112, 0xf94003e9#32)
  | .p116 => (116, 0x910043ff#32)
  | .p120 => (120, 0xaa0a03e9#32)
  | .p124 => (124, 0xd100054a#32)
  | .p128 => (128, 0xb4fffe8b#32)
  | .p132 => (132, 0x91000529#32)
  | .p136 => (136, 0xf100053f#32)
  | .p140 => (140, 0x540017c0#32)
  | .p896 => (896, 0xb4000341#32)
  | .p900 => (900, 0xf9400101#32)
  | .p904 => (904, 0xeb15003f#32)
  | .p908 => (908, 0x54001f88#32)
  | .p912 => (912, 0xb40002c1#32)

def next (s : ArmState) : ArmState := Dispatch.next s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

def WidthOp.effect (base : BitVec 64) : WidthOp → ArmState → ArmState
  | .p60, s => Dispatch.compare32 ((r (.GPR 9#5) s).setWidth 32) 1#32 s
  | .p64, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 68#64 else base + 348#64) s
  | .p68, s => w (.GPR 1#5) (read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s)
      (put 8 (read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s) s)
  | .p72, s => w .PC (if r (.GPR 8#5) s = 0#64 then base + 904#64 else base + 76#64) s
  | .p76, s => put 10 (r (.GPR 1#5) s - 1#64) s
  | .p80, s => write_pstate (AddWithCarry (r (.GPR 10#5) s) 1#64 0#1).2 (next s)
  | .p84, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 896#64 else base + 88#64) s
  | .p88, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p92, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p96, s => put 9 (r (.GPR 10#5) s) s
  | .p100, s => put 9 (r (.GPR 9#5) s <<< 3) s
  | .p104, s => put 9 (r (.GPR 8#5) s + r (.GPR 9#5) s) s
  | .p108, s => put 11 (read_mem_bytes 8 (r (.GPR 9#5) s) s) s
  | .p112, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p116, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p120, s => put 9 (r (.GPR 10#5) s) s
  | .p124, s => put 10 (r (.GPR 10#5) s - 1#64) s
  | .p128, s => w .PC (if r (.GPR 11#5) s = 0#64 then base + 80#64 else base + 132#64) s
  | .p132, s => put 9 (r (.GPR 9#5) s + 1#64) s
  | .p136, s => Dispatch.compare64 (r (.GPR 9#5) s) 1#64 s
  | .p140, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 900#64 else base + 144#64) s
  | .p896, s => w .PC (if r (.GPR 1#5) s = 0#64 then base + 1000#64 else base + 900#64) s
  | .p900, s => put 1 (read_mem_bytes 8 (r (.GPR 8#5) s) s) s
  | .p904, s => Dispatch.compare64 (r (.GPR 1#5) s) (r (.GPR 21#5) s) s
  | .p908, s => w .PC (if r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1
      then base + 1916#64 else base + 912#64) s
  | .p912, s => w .PC (if r (.GPR 1#5) s = 0#64 then base + 1000#64 else base + 916#64) s

end SszArm.Emit.Uint

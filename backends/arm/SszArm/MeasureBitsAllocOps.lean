import SszArm.MeasureContract
import SszArm.NatCompareExec

namespace SszArm.Measure.Bits.Alloc

inductive Site where
  | progressive | bounded | scope
  deriving DecidableEq

inductive Op where
  | loadBase | loadUsed | addAddress | addressGuard | compareAlignment | alignmentGuard
  | addPadding | maskPadding | subtractAddress | addUsed | usedGuard | compareSize
  | sizeGuard | loadCapacity | addSize | compareCapacity | capacityGuard
  | addPointer | finish0 | finish1 | finish2
  deriving DecidableEq

def Site.entry : Site → Nat
  | .progressive => 1500 | .bounded => 1628 | .scope => 3332

def Op.index : Op → Nat
  | .loadBase => 0 | .loadUsed => 1 | .addAddress => 2 | .addressGuard => 3
  | .compareAlignment => 4 | .alignmentGuard => 5 | .addPadding => 6
  | .maskPadding => 7 | .subtractAddress => 8 | .addUsed => 9 | .usedGuard => 10
  | .compareSize => 11 | .sizeGuard => 12 | .loadCapacity => 13 | .addSize => 14
  | .compareCapacity => 15 | .capacityGuard => 16 | .addPointer => 17
  | .finish0 => 18 | .finish1 => 19 | .finish2 => 20

def Site.baseReg : Site → BitVec 5
  | .progressive => 9 | .bounded => 8 | .scope => 10

def Site.usedReg : Site → BitVec 5
  | .progressive => 10 | .bounded => 9 | .scope => 11

def Site.workReg : Site → BitVec 5
  | .progressive => 11 | .bounded => 10 | .scope => 12

def Site.tempReg : Site → BitVec 5
  | .progressive => 12 | .bounded => 11 | .scope => 13

def Site.pointerReg : Site → BitVec 5
  | .progressive | .bounded => 21 | .scope => 10

def Site.countReg : Site → BitVec 5
  | .progressive | .bounded => 24 | .scope => 8

def Site.lowReg : Site → BitVec 5
  | .progressive | .bounded => 26 | .scope => 8

def Site.highReg : Site → BitVec 5
  | .progressive | .bounded => 25 | .scope => 9

def instructionWord : Site → Op → BitVec 32
  | .progressive, .loadBase => 0xf9400289#32
  | .progressive, .loadUsed => 0xf9400a8a#32
  | .progressive, .addAddress => 0xab09014b#32
  | .progressive, .addressGuard => 0x54003f02#32
  | .progressive, .compareAlignment => 0xb100217f#32
  | .progressive, .alignmentGuard => 0x54003ec8#32
  | .progressive, .addPadding => 0x91001d6c#32
  | .progressive, .maskPadding => 0x927df18c#32
  | .progressive, .subtractAddress => 0xcb0b018b#32
  | .progressive, .addUsed => 0xab0a016a#32
  | .progressive, .usedGuard => 0x54003e22#32
  | .progressive, .compareSize => 0xb100455f#32
  | .progressive, .sizeGuard => 0x54003de8#32
  | .progressive, .loadCapacity => 0xf940068c#32
  | .progressive, .addSize => 0x9100414b#32
  | .progressive, .compareCapacity => 0xeb0c017f#32
  | .progressive, .capacityGuard => 0x54003d68#32
  | .progressive, .addPointer => 0x8b0a0135#32
  | .progressive, .finish0 => 0x52800058#32
  | .progressive, .finish1 => 0xf9000a8b#32
  | .progressive, .finish2 => 0xa90066ba#32
  | .bounded, .loadBase => 0xf9400288#32
  | .bounded, .loadUsed => 0xf9400a89#32
  | .bounded, .addAddress => 0xab08012a#32
  | .bounded, .addressGuard => 0x54003b02#32
  | .bounded, .compareAlignment => 0xb100215f#32
  | .bounded, .alignmentGuard => 0x54003ac8#32
  | .bounded, .addPadding => 0x91001d4b#32
  | .bounded, .maskPadding => 0x927df16b#32
  | .bounded, .subtractAddress => 0xcb0a016a#32
  | .bounded, .addUsed => 0xab090149#32
  | .bounded, .usedGuard => 0x54003a22#32
  | .bounded, .compareSize => 0xb100453f#32
  | .bounded, .sizeGuard => 0x540039e8#32
  | .bounded, .loadCapacity => 0xf940068b#32
  | .bounded, .addSize => 0x9100412a#32
  | .bounded, .compareCapacity => 0xeb0b015f#32
  | .bounded, .capacityGuard => 0x54003968#32
  | .bounded, .addPointer => 0x8b090115#32
  | .bounded, .finish0 => 0x52800058#32
  | .bounded, .finish1 => 0xf9000a8a#32
  | .bounded, .finish2 => 0xa90066ba#32
  | .scope, .loadBase => 0xf940028a#32
  | .scope, .loadUsed => 0xf9400a8b#32
  | .scope, .addAddress => 0xab0a016c#32
  | .scope, .addressGuard => 0x540005c2#32
  | .scope, .compareAlignment => 0xb100219f#32
  | .scope, .alignmentGuard => 0x54000588#32
  | .scope, .addPadding => 0x91001d8d#32
  | .scope, .maskPadding => 0x927df1ad#32
  | .scope, .subtractAddress => 0xcb0c01ac#32
  | .scope, .addUsed => 0xab0b018b#32
  | .scope, .usedGuard => 0x540004e2#32
  | .scope, .compareSize => 0xb100457f#32
  | .scope, .sizeGuard => 0x540004a8#32
  | .scope, .loadCapacity => 0xf940068d#32
  | .scope, .addSize => 0x9100416c#32
  | .scope, .compareCapacity => 0xeb0d019f#32
  | .scope, .capacityGuard => 0x54000428#32
  | .scope, .addPointer => 0x8b0b014a#32
  | .scope, .finish0 => 0xf9000a8c#32
  | .scope, .finish1 => 0xa9002548#32
  | .scope, .finish2 => 0x52800048#32

def row (site : Site) (op : Op) : Nat × BitVec 32 :=
  (site.entry + 4 * op.index, instructionWord site op)

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

def commit (site : Site) (s : ArmState) : ArmState :=
  next (write_mem_bytes 8 (r (.GPR 20#5) s + 16#64) (r (.GPR site.workReg) s) s)

def storeWords (site : Site) (s : ArmState) : ArmState :=
  next (write_mem_bytes 16 (r (.GPR site.pointerReg) s)
    (r (.GPR site.highReg) s ++ r (.GPR site.lowReg) s) s)

def effect (site : Site) (base : BitVec 64) : Op → ArmState → ArmState
  | .loadBase, s => put site.baseReg (read_mem_bytes 8 (r (.GPR 20#5) s) s) s
  | .loadUsed, s => put site.usedReg (read_mem_bytes 8 (r (.GPR 20#5) s + 16#64) s) s
  | .addAddress, s => write_pstate
      (AddWithCarry (r (.GPR site.usedReg) s) (r (.GPR site.baseReg) s) 0#1).2
      (put site.workReg (r (.GPR site.usedReg) s + r (.GPR site.baseReg) s) s)
  | .addressGuard, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 3528#64
      else base + BitVec.ofNat 64 (site.entry + 16)) s
  | .compareAlignment, s => write_pstate
      (AddWithCarry (r (.GPR site.workReg) s) 8#64 0#1).2 (next s)
  | .alignmentGuard, s => w .PC
      (if r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1 then base + 3528#64
      else base + BitVec.ofNat 64 (site.entry + 24)) s
  | .addPadding, s => put site.tempReg (r (.GPR site.workReg) s + 7#64) s
  | .maskPadding, s => put site.tempReg (r (.GPR site.tempReg) s &&& 18446744073709551608#64) s
  | .subtractAddress, s => put site.workReg (r (.GPR site.tempReg) s - r (.GPR site.workReg) s) s
  | .addUsed, s => write_pstate
      (AddWithCarry (r (.GPR site.workReg) s) (r (.GPR site.usedReg) s) 0#1).2
      (put site.usedReg (r (.GPR site.workReg) s + r (.GPR site.usedReg) s) s)
  | .usedGuard, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 3528#64
      else base + BitVec.ofNat 64 (site.entry + 44)) s
  | .compareSize, s => write_pstate
      (AddWithCarry (r (.GPR site.usedReg) s) 17#64 0#1).2 (next s)
  | .sizeGuard, s => w .PC
      (if r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1 then base + 3528#64
      else base + BitVec.ofNat 64 (site.entry + 52)) s
  | .loadCapacity, s => put site.tempReg (read_mem_bytes 8 (r (.GPR 20#5) s + 8#64) s) s
  | .addSize, s => put site.workReg (r (.GPR site.usedReg) s + 16#64) s
  | .compareCapacity, s => Udivti3.compare (r (.GPR site.workReg) s) (r (.GPR site.tempReg) s) s
  | .capacityGuard, s => w .PC
      (if r (.FLAG .C) s = 1#1 ∧ r (.FLAG .Z) s = 0#1 then base + 3528#64
      else base + BitVec.ofNat 64 (site.entry + 68)) s
  | .addPointer, s => put site.pointerReg (r (.GPR site.baseReg) s + r (.GPR site.usedReg) s) s
  | .finish0, s => match site with
      | .progressive | .bounded => put site.countReg 2#64 s
      | .scope => commit site s
  | .finish1, s => match site with
      | .progressive | .bounded => commit site s
      | .scope => storeWords site s
  | .finish2, s => match site with
      | .progressive | .bounded => storeWords site s
      | .scope => put site.countReg 2#64 s

end SszArm.Measure.Bits.Alloc

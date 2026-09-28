import SszArm.BoolMemory

namespace SszArm.Dispatch

/-- Actual private codec::deserialize entry and the complete paths to the seven
primitive body entries. Words are from the byte-checked linked ARM image. -/
def program : List (Nat × BitVec 32) := [
  (0, 0xd105c3ff#32),
  (4, 0xa9117bfd#32),
  (8, 0xa9126ffc#32),
  (12, 0xa91367fa#32),
  (16, 0xa9145ff8#32),
  (20, 0xa91557f6#32),
  (24, 0xa9164ff4#32),
  (28, 0xf9400028#32),
  (32, 0xaa0403f3#32),
  (36, 0xf100151f#32),
  (40, 0x540002cd#32),
  (44, 0xf100211f#32),
  (48, 0x540005ad#32),
  (128, 0xf100091f#32),
  (132, 0x540008cc#32),
  (136, 0xb4000ea8#32),
  (140, 0xf100051f#32),
  (144, 0x54003921#32),
  (228, 0xf100191f#32),
  (232, 0x54000a60#32),
  (412, 0xf1000d1f#32),
  (416, 0x54000880#32),
  (420, 0xf100111f#32),
  (424, 0x540032e1#32)]

def CodeAt (s : ArmState) (base : BitVec 64) : Prop :=
  ∀ row ∈ program, s.program.find? (base + BitVec.ofNat 64 row.1) = some row.2

inductive Kind where
  | bool | uint | byteVector | byteList | bitVector | bitList | progressiveBitList
  deriving DecidableEq

def Kind.tag : Kind → BitVec 64
  | .bool => 0 | .uint => 1 | .byteVector => 2 | .byteList => 3
  | .bitVector => 4 | .bitList => 5 | .progressiveBitList => 6

def Kind.entry : Kind → Nat
  | .bool => 604 | .uint => 148 | .byteVector => 1972 | .byteList => 688
  | .bitVector => 428 | .bitList => 2052 | .progressiveBitList => 564

end SszArm.Dispatch

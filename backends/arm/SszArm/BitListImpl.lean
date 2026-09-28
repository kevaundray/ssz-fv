import SszArm.DelimitedImpl

namespace SszArm.BitList

/-- Actual postdispatch entries in the linked deserialize image. -/
def listEntry : Nat := 2052
def progressiveEntry : Nat := 564
def delimitedOffset : BitVec 64 := 10560

def program : List (Nat × BitVec 32) := [
  (564, 0xaa1303e4#32), (568, 0xa9564ff4#32),
  (572, 0xa95557f6#32), (576, 0x91002021#32),
  (580, 0xa9545ff8#32), (584, 0xa95367fa#32),
  (588, 0xa9526ffc#32), (592, 0xa9517bfd#32),
  (596, 0x9105c3ff#32), (600, 0x140009ba#32),
  (2052, 0xa940a029#32), (2056, 0x910243e1#32),
  (2060, 0xaa1303e4#32), (2064, 0xa909a3e9#32),
  (2068, 0x52800028#32), (2072, 0xf9004be8#32),
  (2076, 0x94000849#32), (2080, 0x14000297#32),
  (4732, 0xa9564ff4#32), (4736, 0xa95557f6#32),
  (4740, 0xa9545ff8#32), (4744, 0xa95367fa#32),
  (4748, 0xa9526ffc#32), (4752, 0xa9517bfd#32),
  (4756, 0x9105c3ff#32), (4760, 0xd65f03c0#32)]

def CodeAt (s : ArmState) (base : BitVec 64) : Prop :=
  ∀ row ∈ program, s.program.find? (base + BitVec.ofNat 64 row.1) = some row.2

theorem all_decode : program.all (fun row => (decode_raw_inst row.2).isSome) = true := by decide

end SszArm.BitList

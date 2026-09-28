import SszX86.MeasureOwned

namespace SszX86.Measure.Bits
open SszNative UintCodec

theorem nat_loads (m : DataMem) (pointer : BitVec 64) (operand : NatOperand)
    (stored : NatAt m pointer operand) :
    Mem.loadInt m pointer 8 = some (operand.pointer.toNat : Int) ∧
    Mem.loadInt m (pointer + 8#64) 8 = some (operand.payload.toNat : Int) := by
  constructor
  · simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      widthLoad_eq m pointer.toNat 8 operand.pointer.toNat stored.1
  · simpa only [width_address] using
      widthLoad_eq m (pointer.toNat + 8) 8 operand.payload.toNat stored.2.1

theorem arena_loads (m : DataMem) (header address capacity used : BitVec 64)
    (stored : ArenaAt m header address capacity used) :
    Mem.loadInt m header 8 = some (address.toNat : Int) ∧
    Mem.loadInt m (header + 8#64) 8 = some (capacity.toNat : Int) ∧
    Mem.loadInt m (header + 16#64) 8 = some (used.toNat : Int) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      widthLoad_eq m header.toNat 8 address.toNat stored.1
  · simpa only [width_address] using
      widthLoad_eq m (header.toNat + 8) 8 capacity.toNat stored.2.1
  · simpa only [width_address] using
      widthLoad_eq m (header.toNat + 16) 8 used.toNat stored.2.2

end SszX86.Measure.Bits

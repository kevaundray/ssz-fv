import SszX86.BitVectorWorldLocal
import SszX86.BitVectorEntryOwned

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

theorem World.stack_store {s : MachineData} {saved : Saved} {length : NatOperand} {data : Ssz.Bytes}
    {address capacity initialUsed currentUsed : BitVec 64} {writes : List (Nat × Nat)} {m : DataMem}
    (world : World s saved length data address capacity initialUsed currentUsed writes m)
    (off count : Nat) (value : Int) (inside : off + count ≤ 224) :
    World s saved length data address capacity initialUsed currentUsed writes
      (Mem.storeInt m (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) count value) := by
  have low : 72 ≤ s.regs.rsp.toNat := world.physical.stack_low
  have high : s.regs.rsp.toNat + 368 ≤ 2^64 := world.physical.stack_bound
  have lowBV : 72 ≤ s.regs.rsp.toBitVec.toNat := low
  have highBV : s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64 := high
  have location : (s.regs.rsp.toBitVec + BitVec.ofNat 64 off).toNat = s.regs.rsp.toNat + off := by
    change (s.regs.rsp.toBitVec + BitVec.ofNat 64 off).toNat = s.regs.rsp.toBitVec.toNat + off
    bv_omega
  apply world.store
  · rw [location]
    unfold workStart
    omega
  · rw [location]
    unfold workStart workSize
    omega
  · rw [location]
    omega

/-- The reached divider world includes both real entry stores and the actual
CALL return word. No initial cache or hypothetical helper ownership is assumed. -/
theorem entry_world (s : MachineData) (saved : Saved) (length : NatOperand) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64)
    (owned : Owned s saved length data address capacity used) :
    World s saved length data address capacity used used [] (divisionReady s length ra).dmem := by
  have initial := World.initial s saved length data address capacity used owned
  have source := initial.stack_store 104 8 s.regs.rdx.toBitVec.toInt (by decide)
  have output := source.stack_store 8 8 s.regs.rdi.toBitVec.toInt (by decide)
  have entry : World s saved length data address capacity used used [] (entryState s length).dmem := by
    simpa only [entryState, entryMem] using output
  exact entry.call (u := entryState s length) rfl ra

end SszX86.BitVector

import SszX86.BitVectorLoad
import SszX86.BitVectorWorldStack

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

theorem load_store_word (m : DataMem) (pointer value : BitVec 64) :
    Mem.loadInt (Mem.storeInt m pointer 8 value.toInt) pointer 8 = some (value.toNat : Int) := by
  have observed := observe_store64 m pointer 0 value
  have stored : widthLoad (Mem.storeInt m pointer 8 value.toInt) pointer.toNat 8 = some value.toNat := by
    simpa only [widthLoad, observe, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_zero] using observed
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using widthLoad_eq _ _ _ _ stored

theorem stack_read_store (m : DataMem) (sp : BitVec 64) (readOff readCount storeOff storeCount : Nat)
    (value : Int) (high : sp.toNat + 224 ≤ 2^64)
    (readInside : readOff + readCount ≤ 224) (storeInside : storeOff + storeCount ≤ 224)
    (apart : readOff + readCount ≤ storeOff ∨ storeOff + storeCount ≤ readOff) :
    Mem.loadInt (Mem.storeInt m (sp + BitVec.ofNat 64 storeOff) storeCount value)
      (sp + BitVec.ofNat 64 readOff) readCount =
      Mem.loadInt m (sp + BitVec.ofNat 64 readOff) readCount := by
  apply load_store_disjoint
  intro i hi j hj
  bv_omega

theorem call_stack_read (s : MachineData) (ra : BitVec 64) (off count : Nat)
    (low : 8 ≤ s.regs.rsp.toBitVec.toNat) (high : s.regs.rsp.toBitVec.toNat + 224 ≤ 2^64)
    (inside : off + count ≤ 224) :
    Mem.loadInt (callState s ra).dmem (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) count =
      Mem.loadInt s.dmem (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) count := by
  apply load_store_disjoint
  intro i hi j hj
  bv_omega

theorem entry_cache (s : MachineData) (saved : Saved) (length : NatOperand) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (owned : Owned s saved length data address capacity used) :
    Mem.loadInt (divisionReady s length ra).dmem (s.regs.rsp.toBitVec + 8#64) 8 =
      some (s.regs.rdi.toNat : Int) ∧
    Mem.loadInt (divisionReady s length ra).dmem (s.regs.rsp.toBitVec + 104#64) 8 =
      some (s.regs.rdx.toNat : Int) := by
  have low : 8 ≤ s.regs.rsp.toBitVec.toNat := by
    have h := owned.stack_low
    change 72 ≤ s.regs.rsp.toBitVec.toNat at h
    omega
  have high : s.regs.rsp.toBitVec.toNat + 224 ≤ 2^64 := by
    have h := owned.stack_bound
    change s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64 at h
    omega
  have cacheOut := call_stack_read (entryState s length) ra 8 8 low high (by decide)
  have cacheSource := call_stack_read (entryState s length) ra 104 8 low high (by decide)
  change Mem.loadInt (divisionReady s length ra).dmem (s.regs.rsp.toBitVec + 8#64) 8 =
    Mem.loadInt (entryMem s) (s.regs.rsp.toBitVec + 8#64) 8 at cacheOut
  change Mem.loadInt (divisionReady s length ra).dmem (s.regs.rsp.toBitVec + 104#64) 8 =
    Mem.loadInt (entryMem s) (s.regs.rsp.toBitVec + 104#64) 8 at cacheSource
  constructor
  · rw [cacheOut]
    exact load_store_word _ _ _
  · rw [cacheSource]
    change Mem.loadInt (Mem.storeInt _ (s.regs.rsp.toBitVec + 8#64) 8 s.regs.rdi.toBitVec.toInt)
      (s.regs.rsp.toBitVec + 104#64) 8 = _
    rw [stack_read_store _ _ 104 8 8 8 _ high (by decide) (by decide) (by decide)]
    exact load_store_word _ _ _

end SszX86.BitVector

import SszX86.BitVectorMemory

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def entryMem (s : MachineData) : DataMem :=
  Mem.storeInt (Mem.storeInt s.dmem (s.regs.rsp.toBitVec + 104#64) 8 s.regs.rdx.toBitVec.toInt)
    (s.regs.rsp.toBitVec + 8#64) 8 s.regs.rdi.toBitVec.toInt

def entryState (s : MachineData) (length : NatOperand) : MachineData :=
  {s with
    regs := {s.regs with
      rdi := UInt64.ofBitVec (s.regs.rsp.toBitVec + 16#64)
      rsi := UInt64.ofBitVec length.pointer
      rdx := UInt64.ofBitVec length.payload
      rcx := UInt64.ofBitVec 8#64
      r8 := s.regs.rbx
      r15 := UInt64.ofBitVec length.pointer
      r12 := UInt64.ofBitVec length.payload}
    dmem := entryMem s}

/-- A body-local store preserves every separated immutable load. -/
theorem work_store_load (m : DataMem) (sp : BitVec 64) (p n off count : Nat) (value : Int)
    (low : 72 ≤ sp.toNat) (high : sp.toNat + 368 ≤ 2^64)
    (bound : p + n ≤ 2^64) (apart : Body.Apart p n (sp.toNat - 72) 296)
    (within : off + count ≤ 224) :
    Mem.loadInt (Mem.storeInt m (sp + BitVec.ofNat 64 off) count value) (BitVec.ofNat 64 p) n =
      Mem.loadInt m (BitVec.ofNat 64 p) n := by
  apply BoolCodec.load_store_disjoint
  intro i hi j hj
  unfold Body.Apart at apart
  bv_omega

theorem entry_load (s : MachineData) (saved : Saved) (length : NatOperand)
    (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (owned : Owned s saved length data address capacity used)
    (p n : Nat) (bound : p + n ≤ 2^64) (apart : Body.Apart p n (workStart s) workSize) :
    Mem.loadInt (entryMem s) (BitVec.ofNat 64 p) n = Mem.loadInt s.dmem (BitVec.ofNat 64 p) n := by
  unfold entryMem
  rw [work_store_load _ _ p n 8 8 _ owned.stack_low owned.stack_bound bound apart (by decide)]
  rw [work_store_load _ _ p n 104 8 _ owned.stack_low owned.stack_bound bound apart (by decide)]

theorem entry_descriptor (s : MachineData) (saved : Saved) (length : NatOperand)
    (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (owned : Owned s saved length data address capacity used) :
    Mem.loadInt (entryMem s) (s.regs.rbp.toBitVec + 8#64) 8 = some (length.pointer.toNat : Int) ∧
    Mem.loadInt (entryMem s) (s.regs.rbp.toBitVec + 16#64) 8 = some (length.payload.toNat : Int) := by
  have bound := owned.descriptor_owned.bound
  have apart := owned.descriptor_owned.work
  have pointer := widthLoad_eq _ _ _ _ owned.descriptor.1
  have payload := widthLoad_eq _ _ _ _ owned.descriptor.2.1
  constructor
  · have unchanged := entry_load s saved length data address capacity used owned
      (s.regs.rbp.toNat + 8) 8 (by omega)
      (by unfold Body.Apart at *; omega)
    have result := unchanged.trans pointer
    change Mem.loadInt (entryMem s) (BitVec.ofNat 64 (s.regs.rbp.toBitVec.toNat + 8)) 8 = _ at result
    simpa only [width_address] using result
  · have unchanged := entry_load s saved length data address capacity used owned
      (s.regs.rbp.toNat + 16) 8 (by omega)
      (by unfold Body.Apart at *; omega)
    have result := unchanged.trans (by simpa only [Nat.add_assoc, Nat.reduceAdd] using payload)
    change Mem.loadInt (entryMem s) (BitVec.ofNat 64 (s.regs.rbp.toBitVec.toNat + 16)) 8 = _ at result
    simpa only [width_address] using result

/-- Entry115..152: two actual stack stores, the original descriptor loads, and
the real division argument setup. No intermediate register facts are premises. -/
theorem entry_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (saved : Saved) (length : NatOperand) (data : Ssz.Bytes)
    (address capacity used : BitVec 64) (owned : Owned s saved length data address capacity used)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (entryState s length, base + 152)) :
    Eventually (step e) P (s, base + 115) := by
  have stores := owned.work_mapped
  have load104 : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 104#64) 8 = some old := by
    have h := Large.mapped_load s.dmem (s.regs.rsp.toBitVec - 72#64) workSize 176 8 stores (by decide)
    simpa only [show s.regs.rsp.toBitVec - 72#64 + BitVec.ofNat 64 176 =
      s.regs.rsp.toBitVec + 104#64 by bv_omega] using h
  have load8 : ∃ old, Mem.loadInt
      (Mem.storeInt s.dmem (s.regs.rsp.toBitVec + 104#64) 8 s.regs.rdx.toBitVec.toInt)
      (s.regs.rsp.toBitVec + 8#64) 8 = some old := by
    have hm := Large.mapped_store s.dmem (s.regs.rsp.toBitVec - 72#64)
      (s.regs.rsp.toBitVec + 104#64) workSize 8 s.regs.rdx.toBitVec.toInt stores
    have h := Large.mapped_load _ (s.regs.rsp.toBitVec - 72#64) workSize 80 8 hm (by decide)
    simpa only [show s.regs.rsp.toBitVec - 72#64 + BitVec.ofNat 64 80 =
      s.regs.rsp.toBitVec + 8#64 by bv_omega] using h
  obtain ⟨pointer, payload⟩ := entry_descriptor s saved length data address capacity used owned
  simp only [entryMem] at pointer payload
  bitvector_step 0 using hc
  apply Delimited.store_cps
  · simpa only [BitVec.ofInt_add, BitVec.ofInt_toInt, Width.bytes,
      show BitVec.ofInt 64 104 = 104#64 by decide] using load104
  simp only [Effects.All]
  bitvector_step 1 using hc
  apply Delimited.store_cps
  · simpa only [BitVec.ofInt_add, BitVec.ofInt_toInt, Width.bytes,
      show BitVec.ofInt 64 104 = 104#64 by decide,
      show BitVec.ofInt 64 8 = 8#64 by decide] using load8
  simp only [Effects.All]
  bitvector_step 2 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt,
    show BitVec.ofInt 64 104 = 104#64 by decide,
    show BitVec.ofInt 64 8 = 8#64 by decide]
  bitvector_load pointer
  bitvector_step 3 using hc
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt,
    show BitVec.ofInt 64 16 = 16#64 by decide]
  bitvector_load payload
  bitvector_step 4 using hc
  bitvector_step 5 using hc
  bitvector_step 6 using hc
  bitvector_step 7 using hc
  bitvector_step 8 using hc
  simpa [entryState, entryMem, BitVec.ofInt_add, BitVec.ofInt_toInt,
    show BitVec.ofInt 64 16 = 16#64 by decide,
    show BitVec.ofInt 32 8 = 8#32 by decide] using next

end SszX86.BitVector

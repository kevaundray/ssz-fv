import SszX86.EmitBitsPrepare

namespace SszX86.Emit.Bits
open SszNative.Serialize (Desc Packed)
open UintCodec BoolCodec
open BitVector (constructLow constructQuotient)

def spillMemory (s : MachineData) (bits : Packed) (list : Bool) : DataMem :=
  if list then
    Mem.storeInt (Mem.storeInt s.dmem (s.regs.rsp.toBitVec + 8) 8
      (BitVec.ofNat 64 bits.bytes.size).toInt) (s.regs.rsp.toBitVec + 16) 8
      (constructLow bits.count).toInt
  else Mem.storeInt s.dmem (s.regs.rsp.toBitVec + 8) 8 (constructLow bits.count).toInt

theorem spill_frame (s : MachineData) (bits : Packed) (list : Bool) (size : Nat) :
    MemoryFrame s.dmem (spillMemory s bits list) (BodyWritable s size) := by
  have one (m : DataMem) (byteOffset : Nat) (value : Int) (inside : byteOffset + 8 ≤ 104) :
      MemoryFrame m (Mem.storeInt m (s.regs.rsp.toBitVec + BitVec.ofNat 64 byteOffset) 8 value)
        (BodyWritable s size) := by
    apply frame_mono (store_frame m _ 8 value)
    intro a member
    exact Or.inr (Or.inr (stack_span s byteOffset 8 inside member))
  cases list
  · exact one s.dmem 8 _ (by decide)
  · exact frame_trans (one s.dmem 8 _ (by decide)) (one _ 16 _ (by decide))

theorem spill_mapped (s : MachineData) (bits : Packed) (list : Bool) :
    BitVector.Mapping.Extends s.dmem (spillMemory s bits list) := by
  intro p n mapping
  cases list
  · exact Large.mapped_store _ _ _ _ _ _ mapping
  · exact Large.mapped_store _ _ _ _ _ _ (Large.mapped_store _ _ _ _ _ _ mapping)

theorem stored_word (m : DataMem) (p value : BitVec 64) :
    Mem.loadInt (Mem.storeInt m p 8 value.toInt) p 8 = some (value.toNat : Int) := by
  have observed : widthLoad (Mem.storeInt m p 8 value.toInt) p.toNat 8 = some value.toNat := by
    simpa only [widthLoad, observe, BitVec.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      using observe_store64 m p 0 value
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using widthLoad_eq _ p.toNat 8 value.toNat observed

theorem spill_low (s : MachineData) (bits : Packed) (list : Bool) :
    Mem.loadInt (spillMemory s bits list) (s.regs.rsp.toBitVec + if list then 16 else 8) 8 =
      some ((constructLow bits.count).toNat : Int) := by
  cases list <;> exact stored_word _ _ _

theorem spill_length (s : MachineData) (bits : Packed) (physical : bits.bytes.size < 2^64) :
    Mem.loadInt (spillMemory s bits true) (s.regs.rsp.toBitVec + 8) 8 = some (bits.bytes.size : Int) := by
  unfold spillMemory
  rw [ite_eq_left rfl, load_store_disjoint]
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt physical] using
      stored_word s.dmem (s.regs.rsp.toBitVec + 8) (BitVec.ofNat 64 bits.bytes.size)
  · intro i hi j hj
    bv_omega

theorem Owned.stack_load {s : MachineData} {desc : Desc} {bits : Packed}
    {src : BitVec 64} {size : Nat} (owned : Owned s desc bits src size)
    {m : DataMem} (mapping : BitVector.Mapping.Extends s.dmem m)
    (byteOffset : Nat) (within : byteOffset + 8 ≤ 104) :
    ∃ old, Mem.loadInt m (s.regs.rsp.toBitVec + BitVec.ofNat 64 byteOffset) 8 = some old := by
  have loaded := Large.mapped_load m (s.regs.rsp.toBitVec - 8) 112 (8 + byteOffset) 8
    (mapping _ _ owned.stackMapped) (by omega)
  have address : (s.regs.rsp.toBitVec - 8) + BitVec.ofNat 64 (8 + byteOffset) =
      s.regs.rsp.toBitVec + BitVec.ofNat 64 byteOffset := by bv_omega
  simpa only [address] using loaded

/-- Register and memory image immediately before either real memcpy CALL. -/
def prepared (s : MachineData) (bits : Packed) (src : BitVec 64) (list : Bool)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (constructLow bits.count)
      rcx := if list then UInt64.ofNat bits.bytes.size else s.regs.rcx
      rdx := UInt64.ofBitVec (constructQuotient bits.count)
      rsi := UInt64.ofBitVec src
      rdi := s.regs.r14
      r12 := UInt64.ofBitVec src
      r13 := UInt64.ofBitVec (constructQuotient bits.count)
      r15 := s.regs.r9
      rbp := if list then UInt64.ofNat (bits.count.toNat % 8) else UInt64.ofNat bits.bytes.size}
    dmem := spillMemory s bits list
    status := flags}

end SszX86.Emit.Bits

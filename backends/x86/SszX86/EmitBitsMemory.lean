import SszX86.EmitBitsFacts
import SszX86.EmitMemcpyCall
import SszX86.BitVectorMappingClosure

namespace SszX86.Emit.Bits
open SszNative.Serialize (Desc Packed)
open UintCodec BoolCodec
open BitVector (constructLow constructHigh)

/-- All resources are observations of the incoming PC414 state. Readonly
objects may alias; only the actual result, live output and local stack writes
are excluded. In particular no Plan storage or descriptor-cap limbs are read. -/
structure Owned (s : MachineData) (desc : Desc) (bits : Packed) (src : BitVec 64)
    (size : Nat) : Prop where
  kind : IsBits desc
  valid : ValidCall desc (.bits bits) s.regs.r9.toNat size
  tag : s.regs.rax.toBitVec = BitVec.ofNat 64 (descTag desc)
  physical : bits.bytes.size < 2^64
  pointer : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 16) 8 = some (src.toNat : Int)
  length : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 24) 8 = some (bits.bytes.size : Int)
  low : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 32) 8 =
    some ((constructLow bits.count).toNat : Int)
  high : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 40) 8 =
    some ((constructHigh bits.count).toNat : Int)
  source : BytesAt s.dmem src bits.bytes
  outputMapped : Large.Mapped s.dmem s.regs.r14.toBitVec size
  resultMapped : Large.Mapped s.dmem s.regs.rbx.toBitVec 8
  stackMapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 8) 112
  outputResult : Large.Disjoint s.regs.r14.toBitVec s.regs.rbx.toBitVec size 8
  outputStack : Large.Disjoint s.regs.r14.toBitVec (s.regs.rsp.toBitVec - 8) size 112
  resultStack : Large.Disjoint s.regs.rbx.toBitVec (s.regs.rsp.toBitVec - 8) 8 112
  headerProtected : ∀ a, InSpan a s.regs.r12.toBitVec 48 → ¬ BodyWritable s size a
  sourceProtected : ∀ a, InSpan a src bits.bytes.size → ¬ BodyWritable s size a

theorem frame_refl (m : DataMem) (writable : BitVec 64 → Prop) :
    MemoryFrame m m writable := by intro a outside; rfl

theorem frame_trans {m n p : DataMem} {writable : BitVec 64 → Prop}
    (first : MemoryFrame m n writable) (second : MemoryFrame n p writable) :
    MemoryFrame m p writable := by
  intro a outside
  exact (second a outside).trans (first a outside)

theorem frame_mono {m n : DataMem} {small large : BitVec 64 → Prop}
    (frame : MemoryFrame m n small) (contained : ∀ a, small a → large a) :
    MemoryFrame m n large := by
  intro a outside
  exact frame a (fun inside => outside (contained a inside))

theorem store_frame (m : DataMem) (p : BitVec 64) (byteCount : Nat) (value : Int) :
    MemoryFrame m (Mem.storeInt m p byteCount value) (fun a => InSpan a p byteCount) := by
  intro a outside
  apply memmove_store_lookup_outside
  intro i hi equal
  exact outside ⟨i, by simpa only [Int.toBytes_length] using hi, equal⟩

theorem span_subspan (p : BitVec 64) (byteOffset byteCount limit : Nat)
    (within : byteOffset + byteCount ≤ limit) {a : BitVec 64}
    (inside : InSpan a (p + BitVec.ofNat 64 byteOffset) byteCount) : InSpan a p limit := by
  obtain ⟨i, hi, rfl⟩ := inside
  refine ⟨byteOffset + i, by omega, ?_⟩
  simp only [memmove_addr_add]

theorem stack_span (s : MachineData) (byteOffset byteCount : Nat) (within : byteOffset + byteCount ≤ 104)
    {a : BitVec 64} (inside : InSpan a (s.regs.rsp.toBitVec + BitVec.ofNat 64 byteOffset) byteCount) :
    InSpan a (s.regs.rsp.toBitVec - 8) 112 := by
  obtain ⟨i, hi, rfl⟩ := inside
  refine ⟨8 + byteOffset + i, by omega, ?_⟩
  bv_omega

theorem protected_load {m n : DataMem} {writable : BitVec 64 → Prop}
    (frame : MemoryFrame m n writable) (p : BitVec 64) (byteCount : Nat)
    (readonly : ∀ a, InSpan a p byteCount → ¬ writable a) :
    Mem.loadInt n p byteCount = Mem.loadInt m p byteCount := by
  apply memmove_loadInt_congr
  intro i hi
  exact frame _ (readonly _ ⟨i, hi, rfl⟩)

theorem Owned.header_load {s : MachineData} {desc : Desc} {bits : Packed}
    {src : BitVec 64} {size : Nat} (owned : Owned s desc bits src size)
    {m : DataMem} (frame : MemoryFrame s.dmem m (BodyWritable s size))
    (byteOffset : Nat) (within : byteOffset + 8 ≤ 48) :
    Mem.loadInt m (s.regs.r12.toBitVec + BitVec.ofNat 64 byteOffset) 8 =
      Mem.loadInt s.dmem (s.regs.r12.toBitVec + BitVec.ofNat 64 byteOffset) 8 := by
  apply protected_load frame
  intro a inside
  exact owned.headerProtected a (span_subspan _ _ _ _ within inside)

theorem Owned.source_at {s : MachineData} {desc : Desc} {bits : Packed}
    {src : BitVec 64} {size : Nat} (owned : Owned s desc bits src size)
    {m : DataMem} (frame : MemoryFrame s.dmem m (BodyWritable s size)) :
    BytesAt m src bits.bytes := by
  intro i hi
  rw [frame _ (owned.sourceProtected _ ⟨i, hi, rfl⟩)]
  exact owned.source i hi

def «prefix» (bits : Packed) : Ssz.Bytes := bits.bytes.extract 0 (bits.count.toNat / 8)

theorem prefix_size (bits : Packed) : («prefix» bits).size = bits.count.toNat / 8 := by
  simp only [«prefix», Array.size_extract, Nat.sub_zero,
    Nat.min_eq_left (backing_guards bits).1]

theorem prefix_bytes (bits : Packed) (m : DataMem) (src : BitVec 64)
    (source : BytesAt m src bits.bytes) : ListBytesAt m src («prefix» bits).toList := by
  intro i hi
  have hi' : i < bits.count.toNat / 8 := by simpa only [Array.length_toList, prefix_size] using hi
  have hs : i < bits.bytes.size := Nat.lt_of_lt_of_le hi' (backing_guards bits).1
  rw [List.getElem?_eq_getElem hi]
  simpa [«prefix», Array.getElem_extract] using source i hs

theorem list_prefix_output (bits : Packed) (m : DataMem) (dst : BitVec 64)
    (source : ListBytesAt m dst («prefix» bits).toList) : BytesAt m dst («prefix» bits) := by
  intro i hi
  have read := source i (by simpa only [Array.length_toList] using hi)
  simpa only [Array.getElem?_toList, Array.getElem?_eq_getElem hi] using read

/-- Static ownership implies all three memcpy separation obligations. -/
theorem Owned.copy_apart {s : MachineData} {desc : Desc} {bits : Packed}
    {src : BitVec 64} {size : Nat} (owned : Owned s desc bits src size) :
    Large.Disjoint src s.regs.r14.toBitVec (bits.count.toNat / 8) (bits.count.toNat / 8) ∧
    Large.Disjoint src (s.regs.rsp.toBitVec - 8) (bits.count.toNat / 8) 8 ∧
    Large.Disjoint s.regs.r14.toBitVec (s.regs.rsp.toBitVec - 8) (bits.count.toNat / 8) 8 := by
  have prefixBound := full_le_size owned.kind owned.valid.success
  have backing := (backing_guards bits).1
  refine ⟨?_, ?_, ?_⟩
  · intro i hi j hj equal
    exact owned.sourceProtected _ ⟨i, by omega, rfl⟩
      (Or.inl ⟨j, by omega, equal⟩)
  · intro i hi j hj equal
    exact owned.sourceProtected _ ⟨i, by omega, rfl⟩
      (Or.inr (Or.inr ⟨j, by omega, equal⟩))
  · intro i hi j hj
    exact owned.outputStack i (by omega) j (by omega)

end SszX86.Emit.Bits

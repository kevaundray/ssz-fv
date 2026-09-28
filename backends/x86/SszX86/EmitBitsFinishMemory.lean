import SszX86.EmitBitsMemory
import SszX86.MemsetMemory

namespace SszX86.Emit.Bits
open BoolCodec UintCodec

theorem byte_encoding (byte : UInt8) : Int.toBytes 1 byte.toBitVec.toInt = [byte] := by
  simpa [memsetByteValue, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
    using memset_byte_signed_roundtrip byte

theorem byte_load (m : DataMem) (p : BitVec 64) (byte : UInt8)
    (stored : m.get? p = some byte) : Mem.loadInt m p 1 = some (byte.toNat : Int) := by
  have loaded := memmove_loadInt_of_lookup m p [byte] (by
    intro i hi
    have zero : i = 0 := by simpa using hi
    subst i
    simpa using stored)
  simpa [Int.ofBytes] using loaded

/-- Appending the single canonical or delimiter byte preserves every copied
prefix byte. No input-padding restriction is needed. -/
theorem bytes_append_store (m : DataMem) (p : BitVec 64) (bytes : Ssz.Bytes) (byte : UInt8)
    (bound : bytes.size < 2^64) (copiedBytes : BytesAt m p bytes) :
    BytesAt (Mem.storeInt m (p + BitVec.ofNat 64 bytes.size) 1 byte.toBitVec.toInt)
      p (bytes ++ #[byte]) := by
  intro i hi
  have within : i < bytes.size + 1 := by simpa using hi
  by_cases before : i < bytes.size
  · rw [Mem.storeInt, memmove_store_lookup_outside]
    · simpa only [Array.append_singleton, Array.getElem_push_lt before] using copiedBytes i before
    · intro j hj equal
      have hj' : j < 1 := by simpa only [Int.toBytes_length] using hj
      have zero : j = 0 := by omega
      subst j
      simp only [BitVec.add_zero] at equal
      have same : BitVec.ofNat 64 i = BitVec.ofNat 64 bytes.size :=
        (BitVec.add_right_inj p).mp equal
      have hiBound : i < 2^64 := by omega
      have index := congrArg BitVec.toNat same
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hiBound, Nat.mod_eq_of_lt bound] at index
      omega
  · have equal : i = bytes.size := by omega
    subst i
    have stored := memmove_store_lookup_inside m (p + BitVec.ofNat 64 bytes.size) [byte]
      0 (by simp) (by simp)
    simpa [Mem.storeInt, byte_encoding, Array.getElem_append] using stored

def lengthStored (s : MachineData) (length : Nat) : MachineData :=
  {s with dmem := Mem.storeInt s.dmem s.regs.rbx.toBitVec 8 (BitVec.ofNat 64 length).toInt}

/-- The only result bytes touched before PC1593 are the eight-byte length.
The caller's unused result fields, output tail and all other memory are framed. -/
theorem length_post (s t : MachineData) (bytes : Ssz.Bytes)
    (bound : bytes.size < 2^64) (stack : t.regs.rsp = s.regs.rsp)
    (result : t.regs.rbx = s.regs.rbx) (vector : t.zmms = s.zmms)
    (output : BytesAt t.dmem s.regs.r14.toBitVec bytes)
    (frame : MemoryFrame s.dmem t.dmem (BodyWritable s bytes.size))
    (apart : Large.Disjoint s.regs.r14.toBitVec s.regs.rbx.toBitVec bytes.size 8) :
    BodyPost s bytes (lengthStored t bytes.size) := by
  refine ⟨stack, result, ?_, ?_, ?_, vector⟩
  · have observed := observe_store64 t.dmem s.regs.rbx.toBitVec 0 (BitVec.ofNat 64 bytes.size)
    simpa [lengthStored, result, widthLoad, observe, Nat.mod_eq_of_lt bound] using observed
  · intro i hi
    rw [lengthStored, result, Mem.storeInt, memmove_store_lookup_outside]
    · exact output i hi
    · intro j hj
      exact apart i hi j (by simpa only [Int.toBytes_length] using hj)
  · apply frame_trans frame
    apply frame_mono (store_frame t.dmem t.regs.rbx.toBitVec 8 _)
    intro a inside
    exact Or.inr (Or.inl (by simpa only [result] using inside))

/-- Any borrowed observation outside the three exact write regions survives a
body proof, including aliased descriptor/cap/Nat/value/backing observations. -/
theorem BodyPost.readonly {s t : MachineData} {bytes : Ssz.Bytes}
    (post : BodyPost s bytes t) (p : BitVec 64) (byteCount : Nat)
    (readonly : ∀ a, InSpan a p byteCount → ¬ BodyWritable s bytes.size a) :
    Mem.loadInt t.dmem p byteCount = Mem.loadInt s.dmem p byteCount :=
  protected_load post.frame p byteCount readonly

end SszX86.Emit.Bits

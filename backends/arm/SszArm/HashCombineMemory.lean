import SszArm.HashCombineCalls

namespace SszArm.Hash.Combine

open SszNative.HashStream (copy)

def sliceBytes (input : ByteArray) (start count : Nat) : ByteArray :=
  ⟨((input.data.toList.drop start).take count).toArray⟩

theorem sliceBytes_size (input : ByteArray) (start count : Nat)
    (bound : start + count ≤ input.size) : (sliceBytes input start count).size = count := by
  simp only [sliceBytes, ByteArray.size, List.size_toArray, List.length_take,
    List.length_drop, Array.length_toList]
  change min count (input.size - start) = count
  omega

theorem bytesAt_slice {s : ArmState} {address : BitVec 64} {input : ByteArray}
    (source : BytesAt s address input) (start count : Nat)
    (bound : start + count ≤ input.size) :
    BytesAt s (address + BitVec.ofNat 64 start) (sliceBytes input start count) := by
  intro i
  have within : i.val < count := by simpa only [sliceBytes_size input start count bound] using i.isLt
  have sourceIndex : start + i.val < input.size := by omega
  have addressEq : address + BitVec.ofNat 64 start + BitVec.ofNat 64 i.val =
      address + BitVec.ofNat 64 (start + i.val) := by bv_omega
  rw [addressEq, source ⟨start + i.val, sourceIndex⟩]
  simp only [sliceBytes, ByteArray.getElem_eq_getElem_data, List.getElem_toArray,
    List.getElem_take, List.getElem_drop, Array.getElem_toList]
  rfl

theorem compress_slice (words : Vector UInt32 8) (input : ByteArray) (start : Nat)
    (bound : start + 64 ≤ input.size) :
    Ssz.Sha256.compress words (sliceBytes input start 64) 0 =
      Ssz.Sha256.compress words input start := by
  exact (SszNative.HashStream.compress_eq_compressList words input start bound).symm

private theorem bytesAt_vector (s : ArmState) (address : BitVec 64)
    (bytes : Vector UInt8 64)
    (observed : ∀ i : Fin 64,
      s.mem (address + BitVec.ofNat 64 i.val) = bytes[i.val].toBitVec) :
    BytesAt s address ⟨bytes.toArray⟩ := by
  intro i
  exact observed ⟨i.val, by simpa only [vectorByteArray_size] using i.isLt⟩

/-- A residual memcpy realizes the existing streaming overwrite, not a fresh
zeroed buffer. Bytes outside the copied interval remain the old buffer bytes. -/
theorem CopyPost.buffer {site : CopySite} {s t : ArmState} (post : CopyPost site s t)
    (buffer inputAddress : BitVec 64) (old : Vector UInt8 64) (input : ByteArray)
    (destination source count : Nat)
    (bufferBound : destination + count ≤ 64) (inputBound : source + count ≤ input.size)
    (bufferPhysical : buffer.toNat + 64 ≤ 2^64)
    (inputPhysical : inputAddress.toNat + input.size ≤ 2^64)
    (bufferAt : BytesAt s buffer ⟨old.toArray⟩) (inputAt : BytesAt s inputAddress input)
    (dst : r (.GPR 0#5) s = buffer + BitVec.ofNat 64 destination)
    (src : r (.GPR 1#5) s = inputAddress + BitVec.ofNat 64 source)
    (length : (r (.GPR 2#5) s).toNat = count) :
    BytesAt t buffer ⟨(copy old destination input source count bufferBound inputBound).toArray⟩ := by
  apply bytesAt_vector
  intro i
  have index : i.val < 64 := i.isLt
  by_cases empty : count = 0
  · rw [post.memory, length, Memcpy.image, if_neg (by omega)]
    rw [SszNative.HashStream.copy_outside _ _ _ _ _ _ _ _ index (by omega)]
    exact bufferAt ⟨i.val, by simpa only [vectorByteArray_size] using index⟩
  have positive : 0 < count := by omega
  have addressNat : (buffer + BitVec.ofNat 64 i.val).toNat = buffer.toNat + i.val := by
    bv_omega
  have destinationNat : (buffer + BitVec.ofNat 64 destination).toNat =
      buffer.toNat + destination := by bv_omega
  rw [post.memory, dst, src, length, Memcpy.image, addressNat, destinationNat]
  by_cases inside : destination ≤ i.val ∧ i.val < destination + count
  · rw [if_pos (by omega)]
    have sourceIndex : source + (i.val - destination) < input.size := by omega
    have addressEq : inputAddress + BitVec.ofNat 64 source +
        BitVec.ofNat 64 (buffer.toNat + i.val - (buffer.toNat + destination)) =
        inputAddress + BitVec.ofNat 64 (source + (i.val - destination)) := by
      bv_omega
    rw [addressEq, inputAt ⟨source + (i.val - destination), sourceIndex⟩]
    rw [SszNative.HashStream.copy_inside _ _ _ _ _ _ _ _ index inside]
  · rw [if_neg (by omega)]
    rw [SszNative.HashStream.copy_outside _ _ _ _ _ _ _ _ index inside]
    exact bufferAt ⟨i.val, by simpa only [vectorByteArray_size] using index⟩

end SszArm.Hash.Combine

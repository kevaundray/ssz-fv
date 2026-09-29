import SszArm.HashBufferMemory

namespace SszArm.Hash

open SszNative.HashStream (overwrite)

/-- Any actual architectural scalar store with a proved byte encoding realizes
an overwrite of the existing source buffer. Empty stores impose no endpoint
nonwrapping requirement beyond the enclosing buffer's physical bound. -/
theorem bytesAt_store (s : ArmState) (address : BitVec 64) (buf : Vector UInt8 64)
    (offset : Nat) (payload : List UInt8) (bound : offset + payload.length ≤ 64)
    (value : BitVec (payload.length * 8))
    (encoding : ∀ i : Fin payload.length, value.extractLsByte i.val = payload[i.val].toBitVec)
    (physical : address.toNat + 64 ≤ 2^64)
    (source : BytesAt s address ⟨buf.toArray⟩) :
    BytesAt (write_mem_bytes payload.length (address + BitVec.ofNat 64 offset) value s)
      address ⟨(overwrite buf offset payload bound).toArray⟩ := by
  apply bytesAt_overwrite address buf offset payload bound source
  intro i
  have hi := i.isLt
  by_cases empty : payload.length = 0
  · have nil : payload = [] := by
      cases payload with
      | nil => rfl
      | cons head tail => simp at empty
    subst payload
    rw [dif_neg (by simp)]
    rfl
  · have offsetBound : offset < 64 := by omega
    have offsetNat : (address + BitVec.ofNat 64 offset).toNat = address.toNat + offset := by
      bv_omega
    have indexNat : (address + BitVec.ofNat 64 i.val).toNat = address.toNat + i.val := by
      bv_omega
    have storeBound : (address + BitVec.ofNat 64 offset).toNat + payload.length ≤ 2^64 := by
      rw [offsetNat]; omega
    rw [Memory.write_mem_bytes_eq_mem_write_bytes]
    change s.mem.write_bytes payload.length (address + BitVec.ofNat 64 offset) value
      (address + BitVec.ofNat 64 i.val) = _
    by_cases inside : offset ≤ i.val ∧ i.val < offset + payload.length
    · rw [dif_pos inside, Memory.write_bytes_eq_extractLsByte
        (ix := address + BitVec.ofNat 64 i.val)
        (base := address + BitVec.ofNat 64 offset) (m := s.mem)
        (n := payload.length) (data := value)
        (by rw [offsetNat, indexNat]; omega) (by rw [offsetNat, indexNat]; omega) storeBound]
      have difference : (address + BitVec.ofNat 64 i.val -
          (address + BitVec.ofNat 64 offset)).toNat = i.val - offset := by bv_omega
      rw [difference]
      exact encoding ⟨i.val - offset, by omega⟩
    · rw [dif_neg inside]
      by_cases before : i.val < offset
      · exact Memory.write_bytes_eq_of_le (by rw [indexNat, offsetNat]; omega) storeBound
      · exact Memory.write_bytes_eq_of_ge (by rw [indexNat, offsetNat]; omega) storeBound

/-- The padding delimiter is the actual one-byte architectural store. -/
theorem bytesAt_delimiter (s : ArmState) (address : BitVec 64) (value : StreamState)
    (physical : address.toNat + 64 ≤ 2^64)
    (source : BytesAt s address ⟨value.buffer.toArray⟩) :
    BytesAt (write_mem_bytes 1 (address + BitVec.ofNat 64 value.buffered.val) 0x80#8 s)
      address ⟨(SszNative.HashStream.delimiterBuffer value).toArray⟩ := by
  apply bytesAt_store s address value.buffer value.buffered.val [0x80] _ 0x80#8 _ physical source
  intro i
  rcases i with ⟨i, hi⟩
  have index : i = 0 := by simp at hi; omega
  subst i
  exact (show (0x80#8).extractLsByte 0 = (0x80 : UInt8).toBitVec from by decide)

end SszArm.Hash

import SszArm.HashMemory

namespace SszArm.Hash

open SszNative.HashStream (overwrite)

/-- Pointwise observation of the existing source overwrite, including its stale tail. -/
theorem overwrite_byte (buf : Vector UInt8 64) (offset : Nat) (payload : List UInt8)
    (bound : offset + payload.length ≤ 64) (i : Fin 64) :
    (overwrite buf offset payload bound)[i.val] =
      if before : i.val < offset then buf[i.val]
      else if inside : i.val < offset + payload.length then
        payload[i.val - offset]'(by omega)
      else buf[i.val] := by
  have offsetBound : offset ≤ 64 := by omega
  have takeLength : (buf.toList.take offset).length = offset := by simp; omega
  have prefixLength : (buf.toList.take offset ++ payload).length = offset + payload.length := by
    simp only [List.length_append, takeLength]
  have valid : i.val <
      (buf.toList.take offset ++ payload ++ buf.toList.drop (offset + payload.length)).toArray.size := by
    simp only [List.size_toArray, List.length_append, takeLength, List.length_drop,
      Vector.length_toList]
    have hi := i.isLt
    omega
  change (buf.toList.take offset ++ payload ++ buf.toList.drop (offset + payload.length)).toArray[i.val] = _
  rw [List.getElem_toArray]
  by_cases before : i.val < offset
  · rw [List.getElem_append_left (by rw [prefixLength]; omega),
      List.getElem_append_left (by rw [takeLength]; omega)]
    simp only [List.getElem_take, Vector.getElem_toList, before, dite_true]
  · by_cases inside : i.val < offset + payload.length
    · rw [List.getElem_append_left (by rw [prefixLength]; omega),
        List.getElem_append_right (by rw [takeLength]; omega)]
      simp only [takeLength, before, inside, dite_false, dite_true]
    · rw [List.getElem_append_right (by rw [prefixLength]; omega)]
      simp only [List.getElem_drop, prefixLength, before, inside, dite_false]
      have index : offset + payload.length + (i.val - (offset + payload.length)) = i.val := by omega
      simp only [index, Vector.getElem_toList]

/-- A proved machine byte image realizes the source's existing overwrite. -/
theorem bytesAt_overwrite {s t : ArmState} (address : BitVec 64)
    (buf : Vector UInt8 64) (offset : Nat) (payload : List UInt8)
    (bound : offset + payload.length ≤ 64)
    (source : BytesAt s address ⟨buf.toArray⟩)
    (image : ∀ i : Fin 64,
      t.mem (address + BitVec.ofNat 64 i.val) =
        if inside : offset ≤ i.val ∧ i.val < offset + payload.length then
          (payload[i.val - offset]'(by omega)).toBitVec
        else s.mem (address + BitVec.ofNat 64 i.val)) :
    BytesAt t address ⟨(overwrite buf offset payload bound).toArray⟩ := by
  intro i
  have valid : i.val < 64 := by simpa only [vectorByteArray_size] using i.isLt
  change t.mem (address + BitVec.ofNat 64 i.val) =
    (overwrite buf offset payload bound)[i.val].toBitVec
  rw [image ⟨i.val, valid⟩, overwrite_byte buf offset payload bound ⟨i.val, valid⟩]
  by_cases before : i.val < offset
  · simp only [before, dite_true, dif_neg (by omega : ¬ (offset ≤ i.val ∧ i.val < offset + payload.length))]
    exact source ⟨i.val, by simpa only [vectorByteArray_size] using i.isLt⟩
  · by_cases inside : i.val < offset + payload.length
    · rw [dif_pos (by omega : offset ≤ i.val ∧ i.val < offset + payload.length)]
      simp only [before, inside, dite_false, dite_true]
    · rw [dif_neg (by omega : ¬ (offset ≤ i.val ∧ i.val < offset + payload.length))]
      simp only [before, inside, dite_false]
      exact source ⟨i.val, by simpa only [vectorByteArray_size] using i.isLt⟩

/-- The exact memset image clears only the specified portion of a 64-byte buffer. -/
theorem bytesAt_zero {s t : ArmState} (address : BitVec 64) (buf : Vector UInt8 64)
    (offset count : Nat) (bound : offset + count ≤ 64)
    (physical : address.toNat + 64 ≤ 2^64)
    (source : BytesAt s address ⟨buf.toArray⟩)
    (memory : ∀ a, t.mem a = Memset.image s.mem (address + BitVec.ofNat 64 offset) 0#8 count a) :
    BytesAt t address ⟨(overwrite buf offset (List.replicate count 0)
      (by simpa using bound)).toArray⟩ := by
  apply bytesAt_overwrite address buf offset (List.replicate count 0) _ source
  intro i
  have hi := i.isLt
  have addressNat : (address + BitVec.ofNat 64 i.val).toNat = address.toNat + i.val := by bv_omega
  by_cases empty : count = 0
  · subst count
    rw [memory, Memset.image, if_neg (by omega), dif_neg (by simp)]
  · have offsetBound : offset < 64 := by omega
    have offsetNat : (address + BitVec.ofNat 64 offset).toNat = address.toNat + offset := by
      bv_omega
    rw [memory, Memset.image]
    simp only [addressNat, offsetNat, List.length_replicate]
    by_cases inside : offset ≤ i.val ∧ i.val < offset + count
    · rw [if_pos (by omega), dif_pos inside]
      simp
    · rw [if_neg (by omega), dif_neg inside]

end SszArm.Hash

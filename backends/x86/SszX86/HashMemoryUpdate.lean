import SszX86.HashMemoryFacts

namespace SszX86.Hash
open SszNative.HashStream

/-- Concatenating observations adds no ownership restriction between read-only data. -/
theorem bytesAt_append (m : DataMem) (p : BitVec 64) (xs ys : List UInt8)
    (first : BytesAt m p xs)
    (second : BytesAt m (p + BitVec.ofNat 64 xs.length) ys) :
    BytesAt m p (xs ++ ys) := by
  intro i hi
  by_cases before : i < xs.length
  · rw [List.getElem?_append_left before]
    exact first i before
  · have after : xs.length ≤ i := by omega
    have rest : i - xs.length < ys.length := by simp only [List.length_append] at hi; omega
    rw [List.getElem?_append_right after]
    have h := second (i - xs.length) rest
    rw [memmove_addr_add, Nat.add_sub_of_le after] at h
    exact h

/-- Exact bytes written in a buffer interval plus its frame implement the shared overwrite. -/
theorem bytesAt_overwrite (m m' : DataMem) (p : BitVec 64) (buf : Vector UInt8 64)
    (start : Nat) (payload : List UInt8) (bound : start + payload.length ≤ 64)
    (_physical : Physical p 64) (before : BytesAt m p buf.toList)
    (written : BytesAt m' (p + BitVec.ofNat 64 start) payload)
    (frame : MemoryFrame m m' (fun a => InSpan a (p + BitVec.ofNat 64 start) payload.length)) :
    BytesAt m' p (overwrite buf start payload bound).toList := by
  rw [overwrite_toList]
  have prefixBytes : BytesAt m' p (buf.toList.take start) := by
    apply bytesAt_frame m m' p _ _
    · simpa only [List.drop_zero, BitVec.add_zero] using
        bytesAt_slice m p buf.toList 0 start (by simp; omega) before
    · exact frame
    · intro i hi inside
      obtain ⟨j, hj, equal⟩ := inside
      have hi' : i < start := by simp only [List.length_take, Vector.length_toList] at hi; omega
      rw [memmove_addr_add] at equal
      bv_omega
  have suffix : BytesAt m' (p + BitVec.ofNat 64 (start + payload.length))
      (buf.toList.drop (start + payload.length)) := by
    have hb : BytesAt m (p + BitVec.ofNat 64 (start + payload.length))
        (buf.toList.drop (start + payload.length)) := by
      have droppedLength :
          (buf.toList.drop (start + payload.length)).length = 64 - (start + payload.length) := by
        simp only [List.length_drop, Vector.length_toList]
      simpa only [← droppedLength, List.take_length] using
        bytesAt_slice m p buf.toList (start + payload.length)
          (64 - (start + payload.length)) (by simp; omega) before
    apply bytesAt_frame m m' _ _ _ hb frame
    intro i hi inside
    obtain ⟨j, hj, equal⟩ := inside
    have hi' : i < 64 - (start + payload.length) := by simpa using hi
    simp only [memmove_addr_add] at equal
    bv_omega
  have prefixLength : (buf.toList.take start).length = start := by
    simp only [List.length_take, Vector.length_toList]
    omega
  apply bytesAt_append
  · apply bytesAt_append m' p _ _ prefixBytes
    simpa only [prefixLength] using written
  · simpa only [List.length_append, prefixLength] using suffix

/-- State reconstruction uses the four exact physical fields, not a future execution. -/
theorem stateAt_of_fields (m : DataMem) (p : BitVec 64) (state : Model)
    (buffer : BytesAt m p state.buffer.toList)
    (chaining : ChainingAt m (p + 64) state.chaining)
    (buffered : ∀ i < 8, m.get? (p + BitVec.ofNat 64 (96 + i)) =
      some (littleByte state.buffered.val i))
    (byteLen : ∀ i < 8, m.get? (p + BitVec.ofNat 64 (104 + i)) =
      some (littleByte state.byteLen.toNat i)) : StateAt m p state := by
  intro i hi
  have hi' : i < 112 := by simpa using hi
  rw [List.getElem?_eq_getElem hi]
  simp only [Vector.getElem_toList]
  by_cases inBuffer : i < 64
  · rw [stateBytes_buffer state i inBuffer]
    have bufferBound : i < state.buffer.toList.length := by
      simpa only [Vector.length_toList] using inBuffer
    have hb := buffer i bufferBound
    rw [List.getElem?_eq_getElem bufferBound, Vector.getElem_toList] at hb
    exact hb
  · by_cases inChaining : i < 96
    · let wordIndex := (i - 64) / 4
      let lane := (i - 64) % 4
      have wordBound : wordIndex < 8 := by dsimp [wordIndex]; omega
      have laneBound : lane < 4 := Nat.mod_lt _ (by decide)
      have split : 64 + 4 * wordIndex + lane = i := by dsimp [wordIndex, lane]; omega
      have hb := chaining (4 * wordIndex + lane) (by simp only [chainingBytes_length]; omega)
      rw [chainingBytes_byte state.chaining wordIndex lane wordBound laneBound] at hb
      have stateByte := stateBytes_chaining state wordIndex lane wordBound laneBound
      simp only [split] at stateByte
      rw [stateByte]
      change m.get? (p + BitVec.ofNat 64 64 + BitVec.ofNat 64 (4 * wordIndex + lane)) = _ at hb
      simpa only [memmove_addr_add, ← Nat.add_assoc, split] using hb
    · by_cases inIndex : i < 104
      · have bound : i - 96 < 8 := by omega
        have split : 96 + (i - 96) = i := by omega
        have stateByte := stateBytes_buffered state (i - 96) bound
        simp only [split] at stateByte
        rw [stateByte]
        simpa only [split] using buffered (i - 96) bound
      · have bound : i - 104 < 8 := by omega
        have split : 104 + (i - 104) = i := by omega
        have stateByte := stateBytes_byteLen state (i - 104) bound
        simp only [split] at stateByte
        rw [stateByte]
        simpa only [split] using byteLen (i - 104) bound

/-- Real memcpy's exact destination observation implements the shared stale-tail copy. -/
theorem bytesAt_copy (m m' : DataMem) (p : BitVec 64) (buf : Vector UInt8 64)
    (dst : Nat) (input : ByteArray) (src count : Nat)
    (hd : dst + count ≤ 64) (hs : src + count ≤ input.size)
    (_physical : Physical p 64) (before : BytesAt m p buf.toList)
    (written : BytesAt m' (p + BitVec.ofNat 64 dst)
      ((input.data.toList.drop src).take count))
    (frame : MemoryFrame m m' (fun a => InSpan a (p + BitVec.ofNat 64 dst) count)) :
    BytesAt m' p (copy buf dst input src count hd hs).toList := by
  intro i hi
  have hi' : i < 64 := by simpa using hi
  rw [List.getElem?_eq_getElem hi]
  simp only [Vector.getElem_toList]
  by_cases inside : dst ≤ i ∧ i < dst + count
  · rw [copy_inside buf dst input src count hd hs i hi' inside]
    have hj : i - dst < count := by omega
    have h := written (i - dst) (by
      rw [memmove_chunk_length _ src count (by simpa using hs)]
      exact hj)
    rw [memmove_addr_add, Nat.add_sub_of_le inside.1,
      memmove_chunk_lookup _ src count (i - dst) hj] at h
    have inputBound : src + (i - dst) < input.data.toList.length := by
      change src + (i - dst) < input.size
      omega
    rw [List.getElem?_eq_getElem inputBound, Array.getElem_toList] at h
    exact h
  · rw [copy_outside buf dst input src count hd hs i hi' inside]
    rw [frame _ (by
      rintro ⟨j, hj, equal⟩
      rw [memmove_addr_add] at equal
      have offset : i = dst + j := by bv_omega
      exact inside (by omega))]
    have bufferBound : i < buf.toList.length := by
      simpa only [Vector.length_toList] using hi'
    have hb := before i bufferBound
    rw [List.getElem?_eq_getElem bufferBound, Vector.getElem_toList] at hb
    exact hb

/-- Unsigned loads are normalized after reading; high-bit-set values stay legal. -/
theorem scalar_bytes_value (byteCount value : Nat) (bound : value < 2 ^ (8 * byteCount)) :
    Int.ofBytes (Int.toBytes byteCount (Int.ofNat value)) = Int.ofNat value := by
  rw [ofBytes_toBytes]
  change (value : Int) % 2 ^ (8 * byteCount) = value
  apply Int.emod_eq_of_lt
  · omega
  · simpa using (Int.ofNat_lt.mpr bound)

end SszX86.Hash

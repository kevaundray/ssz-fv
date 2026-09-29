import SszX86.HashMemoryUpdate

namespace SszX86.Hash
open SszNative.HashStream

/-- Frame transport for one field, retaining the exact stale bytes of every other field. -/
theorem stateAt_replace_chaining (m m' : DataMem) (p : BitVec 64) (state : Model)
    (words : Vector UInt32 8) (extra : BitVec 64 → Prop)
    (_physical : Physical p 112) (before : StateAt m p state)
    (written : ChainingAt m' (p + 64) words)
    (frame : MemoryFrame m m' (fun a => InSpan a (p + 64) 32 ∨ extra a))
    (safe : ∀ i < 112, ¬ extra (p + BitVec.ofNat 64 i)) :
    StateAt m' p { state with chaining := words } := by
  have unchanged (i : Nat) (hi : i < 112) (outside : i < 64 ∨ 96 ≤ i) :
      m'.get? (p + BitVec.ofNat 64 i) = m.get? (p + BitVec.ofNat 64 i) := by
    apply frame
    rintro (⟨j, hj, equal⟩ | other)
    · change p + BitVec.ofNat 64 i = p + BitVec.ofNat 64 64 + BitVec.ofNat 64 j at equal
      rw [memmove_addr_add] at equal
      bv_omega
    · exact safe i hi other
  apply stateAt_of_fields
  · intro i hi
    have hi' : i < 64 := by simpa using hi
    rw [unchanged i (by omega) (Or.inl hi')]
    exact stateAt_buffer m p state before i hi
  · exact written
  · intro i hi
    rw [unchanged (96 + i) (by omega) (Or.inr (by omega))]
    simpa only [stateBytes_buffered state i hi] using
      stateAt_byte m p state before (96 + i) (by omega)
  · intro i hi
    rw [unchanged (104 + i) (by omega) (Or.inr (by omega))]
    simpa only [stateBytes_byteLen state i hi] using
      stateAt_byte m p state before (104 + i) (by omega)

/-- Buffer replacement does not refresh chaining words or either scalar field. -/
theorem stateAt_replace_buffer (m m' : DataMem) (p : BitVec 64) (state : Model)
    (buffer : Vector UInt8 64) (extra : BitVec 64 → Prop)
    (_physical : Physical p 112) (before : StateAt m p state)
    (written : BytesAt m' p buffer.toList)
    (frame : MemoryFrame m m' (fun a => InSpan a p 64 ∨ extra a))
    (safe : ∀ i < 112, ¬ extra (p + BitVec.ofNat 64 i)) :
    StateAt m' p { state with buffer := buffer } := by
  have unchanged (i : Nat) (hi : i < 112) (outside : 64 ≤ i) :
      m'.get? (p + BitVec.ofNat 64 i) = m.get? (p + BitVec.ofNat 64 i) := by
    apply frame
    rintro (⟨j, hj, equal⟩ | other)
    · bv_omega
    · exact safe i hi other
  apply stateAt_of_fields
  · exact written
  · intro i hi
    have hi' : i < 32 := by simpa only [chainingBytes_length] using hi
    have address : p + 64 + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (64 + i) :=
      memmove_addr_add p 64 i
    rw [address, unchanged (64 + i) (by omega) (by omega)]
    simpa only [address] using stateAt_chaining m p state before i hi
  · intro i hi
    rw [unchanged (96 + i) (by omega) (by omega)]
    simpa only [stateBytes_buffered state i hi] using
      stateAt_byte m p state before (96 + i) (by omega)
  · intro i hi
    rw [unchanged (104 + i) (by omega) (by omega)]
    simpa only [stateBytes_byteLen state i hi] using
      stateAt_byte m p state before (104 + i) (by omega)

/-- The actual buffered-count qword store, with every other state byte framed. -/
theorem stateAt_store_buffered (m : DataMem) (p : BitVec 64) (state : Model)
    (count : Fin 64) (_physical : Physical p 112) (before : StateAt m p state) :
    StateAt (Mem.storeInt m (p + 96) 8 (BitVec.ofNat 64 count.val).toInt) p
      { state with buffered := count } := by
  let m' := Mem.storeInt m (p + 96) 8 (BitVec.ofNat 64 count.val).toInt
  have unchanged (i : Nat) (hi : i < 112) (outside : i < 96 ∨ 104 ≤ i) :
      m'.get? (p + BitVec.ofNat 64 i) = m.get? (p + BitVec.ofNat 64 i) := by
    apply storeInt_frame
    rintro ⟨j, hj, equal⟩
    change p + BitVec.ofNat 64 i = p + BitVec.ofNat 64 96 + BitVec.ofNat 64 j at equal
    rw [memmove_addr_add] at equal
    bv_omega
  apply stateAt_of_fields
  · intro i hi
    rw [unchanged i (by simp at hi; omega) (Or.inl (by simp at hi; omega))]
    exact stateAt_buffer m p state before i hi
  · intro i hi
    have hi' : i < 32 := by simpa only [chainingBytes_length] using hi
    have address : p + 64 + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (64 + i) :=
      memmove_addr_add p 64 i
    rw [address, unchanged (64 + i) (by omega) (Or.inl (by omega))]
    simpa only [address] using stateAt_chaining m p state before i hi
  · intro i hi
    have countBound : count.val < 2 ^ 64 := by have h := count.isLt; omega
    have address : p + 96 + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (96 + i) :=
      memmove_addr_add p 96 i
    simpa only [address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound] using
      word_store_bytes m (p + 96) (BitVec.ofNat 64 count.val) i hi
  · intro i hi
    rw [unchanged (104 + i) (by omega) (Or.inr (by omega))]
    simpa only [stateBytes_byteLen state i hi] using
      stateAt_byte m p state before (104 + i) (by omega)

/-- Logical length addition may wrap; the store records the UInt64 field verbatim. -/
theorem stateAt_store_byteLen (m : DataMem) (p : BitVec 64) (state : Model)
    (length : UInt64) (_physical : Physical p 112) (before : StateAt m p state) :
    StateAt (Mem.storeInt m (p + 104) 8 length.toBitVec.toInt) p
      { state with byteLen := length } := by
  let m' := Mem.storeInt m (p + 104) 8 length.toBitVec.toInt
  have unchanged (i : Nat) (hi : i < 104) :
      m'.get? (p + BitVec.ofNat 64 i) = m.get? (p + BitVec.ofNat 64 i) := by
    apply storeInt_frame
    rintro ⟨j, hj, equal⟩
    change p + BitVec.ofNat 64 i = p + BitVec.ofNat 64 104 + BitVec.ofNat 64 j at equal
    rw [memmove_addr_add] at equal
    bv_omega
  apply stateAt_of_fields
  · intro i hi
    rw [unchanged i (by simp at hi; omega)]
    exact stateAt_buffer m p state before i hi
  · intro i hi
    have hi' : i < 32 := by simpa only [chainingBytes_length] using hi
    have address : p + 64 + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (64 + i) :=
      memmove_addr_add p 64 i
    rw [address, unchanged (64 + i) (by omega)]
    simpa only [address] using stateAt_chaining m p state before i hi
  · intro i hi
    rw [unchanged (96 + i) (by omega)]
    simpa only [stateBytes_buffered state i hi] using
      stateAt_byte m p state before (96 + i) (by omega)
  · intro i hi
    have address : p + 104 + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (104 + i) :=
      memmove_addr_add p 104 i
    simpa only [address, UInt64.toNat_toBitVec] using
      word_store_bytes m (p + 104) length.toBitVec i hi

/-- A transient raw occupancy of 64 needs no second semantic State. After
compression and reset, reconstruct from the unchanged buffer/length and the
two newly observed fields. -/
theorem stateAt_replace_chaining_buffered (m m' : DataMem) (p : BitVec 64)
    (state : Model) (words : Vector UInt32 8) (count : Fin 64)
    (extra : BitVec 64 → Prop) (_physical : Physical p 112)
    (before : StateAt m p state) (chaining : ChainingAt m' (p + 64) words)
    (buffered : ∀ i < 8, m'.get? (p + BitVec.ofNat 64 (96 + i)) =
      some (littleByte count.val i))
    (frame : MemoryFrame m m' (fun a => InSpan a (p + 64) 40 ∨ extra a))
    (safe : ∀ i < 112, ¬ extra (p + BitVec.ofNat 64 i)) :
    StateAt m' p { state with chaining := words, buffered := count } := by
  have unchanged (i : Nat) (hi : i < 112) (outside : i < 64 ∨ 104 ≤ i) :
      m'.get? (p + BitVec.ofNat 64 i) = m.get? (p + BitVec.ofNat 64 i) := by
    apply frame
    rintro (⟨j, hj, equal⟩ | other)
    · change p + BitVec.ofNat 64 i = p + BitVec.ofNat 64 64 + BitVec.ofNat 64 j at equal
      rw [memmove_addr_add] at equal
      bv_omega
    · exact safe i hi other
  apply stateAt_of_fields
  · intro i hi
    have hi' : i < 64 := by simpa using hi
    rw [unchanged i (by omega) (Or.inl hi')]
    exact stateAt_buffer m p state before i hi
  · exact chaining
  · exact buffered
  · intro i hi
    rw [unchanged (104 + i) (by omega) (Or.inr (by omega))]
    simpa only [stateBytes_byteLen state i hi] using
      stateAt_byte m p state before (104 + i) (by omega)

end SszX86.Hash

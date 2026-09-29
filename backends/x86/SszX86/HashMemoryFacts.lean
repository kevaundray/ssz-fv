import SszX86.HashMemory
import SszLimbs

namespace SszX86.Hash
open SszNative.HashStream

 theorem bytesAt_load (m : DataMem) (p : BitVec 64) (bytes : List UInt8)
    (h : BytesAt m p bytes) :
    Mem.loadInt m p bytes.length = some (Int.ofBytes bytes) :=
  memmove_loadInt_of_lookup m p bytes h

theorem bytesAt_mapped (m : DataMem) (p : BitVec 64) (bytes : List UInt8)
    (h : BytesAt m p bytes) : Mapped m p bytes.length := by
  intro i hi
  exact ⟨bytes[i], by simpa only [List.getElem?_eq_getElem hi] using h i hi⟩

theorem bytesAt_slice (m : DataMem) (p : BitVec 64) (bytes : List UInt8)
    (start count : Nat) (bound : start + count ≤ bytes.length)
    (h : BytesAt m p bytes) :
    BytesAt m (p + BitVec.ofNat 64 start) ((bytes.drop start).take count) := by
  intro i hi
  have hi' : i < count := by
    simpa only [memmove_chunk_length bytes start count bound] using hi
  rw [memmove_addr_add, memmove_chunk_lookup _ _ _ _ hi']
  exact h (start + i) (by omega)

theorem bytesAt_frame (m m' : DataMem) (p : BitVec 64) (bytes : List UInt8)
    (writable : BitVec 64 → Prop) (h : BytesAt m p bytes)
    (frame : MemoryFrame m m' writable)
    (safe : ∀ i < bytes.length, ¬ writable (p + BitVec.ofNat 64 i)) :
    BytesAt m' p bytes := by
  intro i hi
  rw [frame _ (safe i hi)]
  exact h i hi

theorem mapped_subrange (m : DataMem) (p : BitVec 64) (total start count : Nat)
    (h : Mapped m p total) (bound : start + count ≤ total) :
    Mapped m (p + BitVec.ofNat 64 start) count := by
  intro i hi
  rw [memmove_addr_add]
  exact h (start + i) (by omega)

theorem disjoint_symm (p q : BitVec 64) (n k : Nat)
    (h : Disjoint p q n k) : Disjoint q p k n := by
  intro i hi j hj
  exact Ne.symm (h j hj i hi)

theorem disjoint_subrange (p q : BitVec 64) (n k a b c d : Nat)
    (h : Disjoint p q n k) (ha : a + b ≤ n) (hc : c + d ≤ k) :
    Disjoint (p + BitVec.ofNat 64 a) (q + BitVec.ofNat 64 c) b d := by
  intro i hi j hj
  simp only [memmove_addr_add]
  exact h (a + i) (by omega) (c + j) (by omega)

theorem stack_subrange (m : DataMem) (sp : BitVec 64) (depth used child : Nat)
    (h : StackAt m sp depth) (bound : used + child ≤ depth) :
    StackAt m (sp - BitVec.ofNat 64 used) child := by
  refine ⟨?_, ?_⟩
  · have hs := h.1
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  · have sub := mapped_subrange m (sp - BitVec.ofNat 64 depth) depth
      (depth - (used + child)) child h.2 (by omega)
    have equal : sp - BitVec.ofNat 64 depth + BitVec.ofNat 64 (depth - (used + child)) =
        (sp - BitVec.ofNat 64 used) - BitVec.ofNat 64 child := by
      have hs := h.1
      bv_omega
    simpa only [equal] using sub

theorem storeInt_bytes (m : DataMem) (p : BitVec 64) (byteCount : Nat) (value : Int)
    (bound : byteCount ≤ 2 ^ 64) :
    BytesAt (Mem.storeInt m p byteCount value) p (Int.toBytes byteCount value) := by
  intro i hi
  exact memmove_store_lookup_inside m p _ i hi (by simpa only [Int.toBytes_length] using bound)

theorem storeInt_frame (m : DataMem) (p : BitVec 64) (byteCount : Nat) (value : Int) :
    MemoryFrame m (Mem.storeInt m p byteCount value) (fun a => InSpan a p byteCount) := by
  intro a outside
  apply memmove_store_lookup_outside
  intro i hi equal
  exact outside ⟨i, by simpa only [Int.toBytes_length] using hi, equal⟩

theorem frame_trans (m m' m'' : DataMem) (A B : BitVec 64 → Prop)
    (first : MemoryFrame m m' A) (second : MemoryFrame m' m'' B) :
    MemoryFrame m m'' (fun a => A a ∨ B a) := by
  intro a ha
  exact (second a (fun h => ha (Or.inr h))).trans (first a (fun h => ha (Or.inl h)))

theorem frame_mono (m m' : DataMem) (A B : BitVec 64 → Prop)
    (h : MemoryFrame m m' A) (within : ∀ a, A a → B a) :
    MemoryFrame m m' B := by
  intro a ha
  exact h a (fun hA => ha (within a hA))

/-- An exact overwrite keeps every previously mapped address mapped. -/
theorem mapped_overwrite (m m' : DataMem) (dst : BitVec 64) (bytes : List UInt8)
    (written : BytesAt m' dst bytes)
    (frame : MemoryFrame m m' (fun a => InSpan a dst bytes.length))
    (p : BitVec 64) (n : Nat) (mapping : Mapped m p n) : Mapped m' p n := by
  intro i hi
  by_cases inside : InSpan (p + BitVec.ofNat 64 i) dst bytes.length
  · obtain ⟨j, hj, equal⟩ := inside
    refine ⟨bytes[j], ?_⟩
    rw [equal]
    simpa only [List.getElem?_eq_getElem hj] using written j hj
  · obtain ⟨b, hb⟩ := mapping i hi
    exact ⟨b, (frame _ inside).trans hb⟩

/-- Kraken's scalar byte encoder agrees with the shared layout's byte function. -/
theorem scalar_byte (byteCount value lane : Nat) (hl : lane < byteCount) :
    (Int.toBytes byteCount (Int.ofNat value))[lane]? = some (littleByte value lane) := by
  have laneBound : lane < (Ssz.uintBytes byteCount value).toList.length := by
    simpa only [Array.length_toList, Ssz.uintBytes_size] using hl
  rw [← uintBytes_eq_toBytes, List.getElem?_eq_getElem laneBound, Array.getElem_toList]
  rw [SszNative.Limbs.uintBytes_byte byteCount value lane hl]
  have power : 2 ^ (8 * lane) = 256 ^ lane := by
    rw [show (256 : Nat) = 2 ^ 8 by decide, Nat.pow_mul]
  rw [power]
  exact congrArg some (UInt8.ofNat_mod_size (x := value / 256 ^ lane))

theorem scalar_load (m : DataMem) (p : BitVec 64) (byteCount value : Nat)
    (h : ∀ i < byteCount, m.get? (p + BitVec.ofNat 64 i) = some (littleByte value i)) :
    Mem.loadInt m p byteCount = some (Int.ofBytes (Int.toBytes byteCount (Int.ofNat value))) := by
  have hb : BytesAt m p (Int.toBytes byteCount (Int.ofNat value)) := by
    intro i hi
    have hi' : i < byteCount := by simpa only [Int.toBytes_length] using hi
    rw [scalar_byte byteCount value i hi']
    exact h i hi'
  simpa only [Int.toBytes_length] using bytesAt_load m p _ hb

theorem stateAt_byte (m : DataMem) (p : BitVec 64) (state : Model)
    (h : StateAt m p state) (i : Nat) (hi : i < 112) :
    m.get? (p + BitVec.ofNat 64 i) = some ((stateBytes state)[i]) := by
  have bound : i < (stateBytes state).toList.length := by
    simpa only [Vector.length_toList] using hi
  have byte := h i bound
  rw [List.getElem?_eq_getElem bound, Vector.getElem_toList] at byte
  exact byte

theorem stateAt_buffer (m : DataMem) (p : BitVec 64) (state : Model)
    (h : StateAt m p state) : BytesAt m p state.buffer.toList := by
  intro i hi
  have hi' : i < 64 := by simpa using hi
  rw [List.getElem?_eq_getElem hi]
  simpa only [Vector.getElem_toList, stateBytes_buffer state i hi'] using
    stateAt_byte m p state h i (by omega)

theorem stateAt_mapped (m : DataMem) (p : BitVec 64) (state : Model)
    (h : StateAt m p state) : Mapped m p 112 := by
  simpa only [Vector.length_toList] using bytesAt_mapped m p (stateBytes state).toList h

theorem stateAt_buffered (m : DataMem) (p : BitVec 64) (state : Model)
    (h : StateAt m p state) :
    Mem.loadInt m (p + 96) 8 =
      some (Int.ofBytes (Int.toBytes 8 (Int.ofNat state.buffered.val))) := by
  apply scalar_load
  intro i hi
  change m.get? (p + BitVec.ofNat 64 96 + BitVec.ofNat 64 i) = _
  rw [memmove_addr_add]
  simpa only [stateBytes_buffered state i hi] using
    stateAt_byte m p state h (96 + i) (by omega)

theorem stateAt_byteLen (m : DataMem) (p : BitVec 64) (state : Model)
    (h : StateAt m p state) :
    Mem.loadInt m (p + 104) 8 =
      some (Int.ofBytes (Int.toBytes 8 (Int.ofNat state.byteLen.toNat))) := by
  apply scalar_load
  intro i hi
  change m.get? (p + BitVec.ofNat 64 104 + BitVec.ofNat 64 i) = _
  rw [memmove_addr_add]
  simpa only [stateBytes_byteLen state i hi] using
    stateAt_byte m p state h (104 + i) (by omega)

@[simp] theorem chainingBytes_length (state : Vector UInt32 8) :
    (chainingBytes state).length = 32 := by simp [chainingBytes]

theorem chainingBytes_byte (state : Vector UInt32 8) (i lane : Nat)
    (hi : i < 8) (hl : lane < 4) :
    (chainingBytes state)[4 * i + lane]? = some (littleByte state[i].toNat lane) := by
  have hn : 4 * i + lane < 32 := by omega
  have div : (4 * i + lane) / 4 = i := by omega
  have mod : (4 * i + lane) % 4 = lane := by omega
  simp only [chainingBytes, List.getElem?_ofFn, dite_eq_left hn, div, mod]

theorem stateAt_chaining (m : DataMem) (p : BitVec 64) (state : Model)
    (h : StateAt m p state) : ChainingAt m (p + 64) state.chaining := by
  intro i hi
  have hi' : i < 32 := by simpa only [chainingBytes_length] using hi
  have split : 4 * (i / 4) + i % 4 = i := by omega
  have wordBound : i / 4 < 8 := by omega
  have lane : i % 4 < 4 := Nat.mod_lt _ (by decide)
  have hb := stateAt_byte m p state h (64 + i) (by omega)
  have stateByte := stateBytes_chaining state (i / 4) (i % 4) wordBound lane
  simp only [Nat.add_assoc, split] at stateByte
  rw [stateByte] at hb
  have chainByte := chainingBytes_byte state.chaining (i / 4) (i % 4) wordBound lane
  rw [split] at chainByte
  change m.get? (p + BitVec.ofNat 64 64 + BitVec.ofNat 64 i) = _
  rw [memmove_addr_add, chainByte]
  exact hb

theorem chainingAt_load (m : DataMem) (p : BitVec 64) (state : Vector UInt32 8)
    (h : ChainingAt m p state) (i : Nat) (hi : i < 8) :
    Mem.loadInt m (p + BitVec.ofNat 64 (4 * i)) 4 =
      some (Int.ofBytes (Int.toBytes 4 (Int.ofNat state[i].toNat))) := by
  apply scalar_load
  intro lane hl
  rw [memmove_addr_add]
  have hb := h (4 * i + lane) (by simp only [chainingBytes_length]; omega)
  rw [chainingBytes_byte state i lane hi hl] at hb
  exact hb

/-- Signed qword stores retain the exact unsigned source bytes. -/
theorem word_store_byte (value : BitVec 64) (i : Nat) (hi : i < 8) :
    (Int.toBytes 8 value.toInt)[i]? = some (littleByte value.toNat i) := by
  rw [registerBytes_eq_uintBytes, uintBytes_eq_toBytes]
  exact scalar_byte 8 value.toNat i hi

theorem word_store_bytes (m : DataMem) (p : BitVec 64) (value : BitVec 64)
    (i : Nat) (hi : i < 8) :
    (Mem.storeInt m p 8 value.toInt).get? (p + BitVec.ofNat 64 i) =
      some (littleByte value.toNat i) := by
  have stored := storeInt_bytes m p 8 value.toInt (by decide) i
    (by simpa only [Int.toBytes_length] using hi)
  exact stored.trans (word_store_byte value i hi)

end SszX86.Hash

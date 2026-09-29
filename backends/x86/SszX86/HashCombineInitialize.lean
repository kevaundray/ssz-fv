import SszX86.HashCombineStores
import SszX86.HashInitial

namespace SszX86.Hash.Combine
open SszNative.HashStream

private theorem prepend_qword (m : DataMem) (p : BitVec 64) (bytes : List UInt8)
    (value : BitVec 64) (bound : bytes.length ≤ 104)
    (before : BytesAt m (p + 8) bytes) :
    BytesAt (Mem.storeInt m p 8 value.toInt) p (Int.toBytes 8 value.toInt ++ bytes) := by
  apply bytesAt_append
  · exact storeInt_bytes m p 8 value.toInt (by decide)
  · simp only [Int.toBytes_length]
    apply bytesAt_frame _ _ _ _ _ before (storeInt_frame _ _ _ _)
    intro i hi inside
    rcases inside with ⟨j, hj, equal⟩
    bv_omega

private theorem append_qword (m : DataMem) (p : BitVec 64) (bytes : List UInt8)
    (value : BitVec 64) (bound : bytes.length ≤ 104) (before : BytesAt m p bytes) :
    BytesAt (Mem.storeInt m (p + BitVec.ofNat 64 bytes.length) 8 value.toInt) p
      (bytes ++ Int.toBytes 8 value.toInt) := by
  apply bytesAt_append
  · apply bytesAt_frame _ _ _ _ _ before (storeInt_frame _ _ _ _)
    intro i hi inside
    rcases inside with ⟨j, hj, equal⟩
    bv_omega
  · exact storeInt_bytes _ _ 8 _ (by decide)

private theorem prefix_bytes (m : DataMem) (p : BitVec 64) (xs ys : List UInt8)
    (h : BytesAt m p (xs ++ ys)) : BytesAt m p xs := by
  intro i hi
  have h' := h i (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_left hi] at h'
  exact h'

private theorem suffix_bytes (m : DataMem) (p : BitVec 64) (xs ys : List UInt8)
    (h : BytesAt m p (xs ++ ys)) : BytesAt m (p + BitVec.ofNat 64 xs.length) ys := by
  intro i hi
  have h' := h (xs.length + i) (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at h'
  simpa only [memmove_addr_add] using h'

/-- All eight real zero stores are observed, including the initially stale tail. -/
theorem zero_buffer_bytes (s : MachineData) :
    BytesAt (zeroBuffer s).dmem (s.regs.rsp.toBitVec + 8) (List.replicate 64 0) := by
  let a := storeWord s 64 0
  let b := storeWord a 56 0
  let c := storeWord b 48 0
  let d := storeWord c 40 0
  let f := storeWord d 32 0
  let g := storeWord f 24 0
  let h := storeWord g 16 0
  let k := storeWord h 8 0
  have h1 : BytesAt a.dmem (s.regs.rsp.toBitVec + 64) (Int.toBytes 8 0) :=
    storeInt_bytes _ _ 8 0 (by decide)
  have h2 := prepend_qword a.dmem (s.regs.rsp.toBitVec + 56) _ 0 (by simp [Int.toBytes_length])
    (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h1)
  have h3 := prepend_qword b.dmem (s.regs.rsp.toBitVec + 48) _ 0
    (by simp [Int.toBytes_length]) (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h2)
  have h4 := prepend_qword c.dmem (s.regs.rsp.toBitVec + 40) _ 0
    (by simp [Int.toBytes_length]) (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h3)
  have h5 := prepend_qword d.dmem (s.regs.rsp.toBitVec + 32) _ 0
    (by simp [Int.toBytes_length]) (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h4)
  have h6 := prepend_qword f.dmem (s.regs.rsp.toBitVec + 24) _ 0
    (by simp [Int.toBytes_length]) (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h5)
  have h7 := prepend_qword g.dmem (s.regs.rsp.toBitVec + 16) _ 0
    (by simp [Int.toBytes_length]) (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h6)
  have h8 := prepend_qword h.dmem (s.regs.rsp.toBitVec + 8) _ 0
    (by simp [Int.toBytes_length]) (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h7)
  exact h8

def initialized (s : MachineData) : MachineData :=
  initialCounters (initializedChain (chainPointer (zeroBuffer s)))

/-- The whole state has a concrete byte layout after PC175's counter store. -/
theorem initialized_bytes (s : MachineData) :
    BytesAt (initialized s).dmem (s.regs.rsp.toBitVec + 8)
      (List.replicate 64 0 ++ initialQwordBytes ++ Int.toBytes 8 0 ++
        Int.toBytes 8 s.regs.rdx.toBitVec.toInt) := by
  let p := s.regs.rsp.toBitVec + 8
  let a := chainPointer (zeroBuffer s)
  let b := initialWord a 72 0xbb67ae856a09e667
  let c := initialWord b 80 0xa54ff53a3c6ef372
  let d := initialWord c 88 0x9b05688c510e527f
  let f := initialWord d 96 0x5be0cd191f83d9ab
  let g := storeWord f 104 0
  have h0 : BytesAt a.dmem p (List.replicate 64 0) := zero_buffer_bytes s
  have h1 := append_qword a.dmem p _ 0xbb67ae856a09e667 (by decide) h0
  have h2 := append_qword b.dmem p _ 0xa54ff53a3c6ef372
    (by simp [Int.toBytes_length]) (by
      simpa only [p, List.length_replicate, BitVec.add_assoc, BitVec.reduceAdd] using h1)
  have h3 := append_qword c.dmem p _ 0x9b05688c510e527f
    (by simp [Int.toBytes_length]) (by
      simpa only [p, List.length_append, List.length_replicate, Int.toBytes_length,
        BitVec.add_assoc, BitVec.reduceAdd] using h2)
  have h4 := append_qword d.dmem p _ 0x5be0cd191f83d9ab
    (by simp [Int.toBytes_length]) (by
      simpa only [p, List.length_append, List.length_replicate, Int.toBytes_length,
        BitVec.add_assoc, BitVec.reduceAdd] using h3)
  have h5 := append_qword f.dmem p _ 0
    (by simp [Int.toBytes_length]) (by
      simpa only [p, List.length_append, List.length_replicate, Int.toBytes_length,
        BitVec.add_assoc, BitVec.reduceAdd] using h4)
  have h6 := append_qword g.dmem p _ s.regs.rdx.toBitVec
    (by simp [Int.toBytes_length]) (by
      simpa only [p, List.length_append, List.length_replicate, Int.toBytes_length,
        BitVec.add_assoc, BitVec.reduceAdd] using h5)
  simpa only [initialized, initialCounters, initializedChain, initialWord, storeWord,
    chainPointer, p, a, b, c, d, f, g, initialQwordBytes, initialQwords,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc,
    List.length_append, List.length_replicate, Int.toBytes_length,
    BitVec.add_assoc, BitVec.reduceAdd] using h6

/-- Initialization is the exact shared state, with length already added for
left's first update. High-bit-set physical lengths retain their unsigned bytes. -/
theorem initialized_state (s : MachineData) :
    StateAt (initialized s).dmem (s.regs.rsp.toBitVec + 8) {new with byteLen := s.regs.rdx} := by
  have allBytes := initialized_bytes s
  rw [List.append_assoc, List.append_assoc] at allBytes
  have buffer := prefix_bytes _ _ _ _ allBytes
  have rest := suffix_bytes _ _ _ _ allBytes
  simp only [List.length_replicate] at rest
  have chaining := prefix_bytes _ _ _ _ rest
  have counters := suffix_bytes _ _ _ _ rest
  have ivLength : initialQwordBytes.length = 32 := by
    rw [initial_qwords_bytes, chainingBytes_length]
  have count := prefix_bytes _ _ _ _ counters
  have length := suffix_bytes _ _ _ _ counters
  apply stateAt_of_fields
  · simpa only [new, Vector.toList_replicate] using buffer
  · simpa only [initial_qwords_bytes, BitVec.add_assoc, BitVec.reduceAdd] using chaining
  · intro i hi
    have h := count i (by simpa only [Int.toBytes_length] using hi)
    rw [scalar_byte 8 0 i hi] at h
    simpa only [ivLength, new, memmove_addr_add, Nat.add_assoc, BitVec.add_assoc,
      BitVec.reduceAdd] using h
  · intro i hi
    have h := length i (by simpa only [Int.toBytes_length] using hi)
    rw [word_store_byte s.regs.rdx.toBitVec i hi] at h
    simpa only [ivLength, Int.toBytes_length, UInt64.toNat_toBitVec, new,
      memmove_addr_add, Nat.add_assoc, BitVec.add_assoc, BitVec.reduceAdd] using h

theorem initialized_mapping (s : MachineData) : MappedPreserved s.dmem (initialized s).dmem := by
  intro p n hm
  simp only [initialized, initialCounters, initializedChain, initialWord, chainPointer,
    zeroBuffer, storeWord]
  repeat' first | exact hm | apply Large.mapped_store

theorem initialized_frame (s : MachineData) :
    MemoryFrame s.dmem (initialized s).dmem (DrainWritable s.regs.rsp.toBitVec) := by
  intro a outside
  have unchanged (m : DataMem) (offset : Nat) (value : Int)
      (low : 8 ≤ offset) (high : offset + 8 ≤ 120) :
      (Mem.storeInt m (s.regs.rsp.toBitVec + BitVec.ofNat 64 offset) 8 value).get? a = m.get? a := by
    apply storeInt_frame
    rintro ⟨i, hi, equal⟩
    apply outside
    left
    refine ⟨offset - 8 + i, by omega, ?_⟩
    rw [equal]
    bv_omega
  simp only [initialized, initialCounters, initializedChain, initialWord, chainPointer,
    zeroBuffer, storeWord]
  rw [unchanged _ 112 _ (by decide) (by decide), unchanged _ 104 _ (by decide) (by decide),
    unchanged _ 96 _ (by decide) (by decide), unchanged _ 88 _ (by decide) (by decide),
    unchanged _ 80 _ (by decide) (by decide), unchanged _ 72 _ (by decide) (by decide),
    unchanged _ 8 _ (by decide) (by decide), unchanged _ 16 _ (by decide) (by decide),
    unchanged _ 24 _ (by decide) (by decide), unchanged _ 32 _ (by decide) (by decide),
    unchanged _ 40 _ (by decide) (by decide), unchanged _ 48 _ (by decide) (by decide),
    unchanged _ 56 _ (by decide) (by decide), unchanged _ 64 _ (by decide) (by decide)]

/-- Compose the concrete initialization rows without assuming any initialized
state at entry. Writable bytes may initially contain arbitrary stale values. -/
theorem initialize_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (s : MachineData) (mapping : Mapped s.dmem s.regs.rsp.toBitVec 120)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (initialized s, root + 180)) :
    Eventually (step e) P (s, root + 29) := by
  apply zero_buffer_runs e root hc.combine s mapping
  apply chain_pointer_runs e root hc.combine
  apply initial_chain_runs e root hc.combine
  · simp only [chainPointer, zeroBuffer, storeWord]
    repeat' first | exact mapping | apply Large.mapped_store
  apply initial_counters_runs e root hc.combine
  · simp only [initializedChain, initialWord, chainPointer, zeroBuffer, storeWord]
    repeat' first | exact mapping | apply Large.mapped_store
  exact next

end SszX86.Hash.Combine

import SszX86.UintLimbExec

namespace SszX86.UintCodec.Large
open SszNative
open Std.ExtHashMap

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Source ownership is ordinary mapped byte loads, not an execution hypothesis. -/
def BytesAt (m : DataMem) (src : BitVec 64) (data : Ssz.Bytes) : Prop :=
  ∀ i < data.size, Mem.loadInt m (src + BitVec.ofNat 64 i) 1 =
    some ((data[i]?.getD 0).toNat : Int)

def Mapped (m : DataMem) (dst : BitVec 64) (bytes : Nat) : Prop :=
  ∀ i < bytes, ∃ byte, m.get? (dst + BitVec.ofNat 64 i) = some byte

def Disjoint (src dst : BitVec 64) (length capacity : Nat) : Prop :=
  ∀ i < length, ∀ j < capacity,
    src + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j

/-- Exact sequence of the native limb stores, with no allocation. -/
def fillMem (m : DataMem) (dst : BitVec 64) (index : Nat) :
    List (BitVec 64) → DataMem
  | [] => m
  | word :: rest => fillMem
      (Mem.storeInt m (dst + BitVec.ofNat 64 (8 * index)) 8 word.toInt)
      dst (index + 1) rest

theorem mapped_load (m : DataMem) (dst : BitVec 64) (capacity offset width : Nat)
    (hm : Mapped m dst capacity) (hb : offset + width ≤ capacity) :
    ∃ value, Mem.loadInt m (dst + BitVec.ofNat 64 offset) width = some value := by
  apply memmove_loadInt_exists
  intro i hi
  rw [memmove_addr_add]
  exact hm (offset + i) (by omega)

theorem mapped_store (m : DataMem) (dst address : BitVec 64)
    (capacity width : Nat) (value : Int) (hm : Mapped m dst capacity) :
    Mapped (Mem.storeInt m address width value) dst capacity := by
  intro i hi
  obtain ⟨old, hold⟩ := hm i hi
  change m[dst + BitVec.ofNat 64 i]? = some old at hold
  simp only [Mem.storeInt, Mem.storeBytes, get?_eq_getElem?, union_eq, getElem?_union]
  cases hnew : ((Int.toBytes width value).At address)[dst + BitVec.ofNat 64 i]? with
  | none => exact ⟨old, by simp [hold]⟩
  | some byte => exact ⟨byte, by simp⟩

theorem bytes_store (m : DataMem) (src dst : BitVec 64) (data : Ssz.Bytes)
    (capacity index : Nat) (word : BitVec 64)
    (hs : BytesAt m src data) (hd : Disjoint src dst data.size capacity)
    (hi : 8 * index + 8 ≤ capacity) :
    BytesAt (Mem.storeInt m (dst + BitVec.ofNat 64 (8 * index)) 8 word.toInt)
      src data := by
  intro i hib
  rw [BoolCodec.load_store_disjoint]
  · exact hs i hib
  · intro a ha b hb
    have ha0 : a = 0 := by omega
    subst a
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, memmove_addr_add] using
      hd i hib (8 * index + b) (by omega)

/-- Stores preserve every caller byte outside their enclosing destination. -/
theorem fill_frame (m : DataMem) (dst : BitVec 64) (index : Nat)
    (words : List (BitVec 64)) (address : BitVec 64)
    (ha : ∀ j, 8 * index ≤ j → j < 8 * (index + words.length) →
      address ≠ dst + BitVec.ofNat 64 j) :
    (fillMem m dst index words).get? address = m.get? address := by
  induction words generalizing index m with
  | nil => rfl
  | cons word words ih =>
    rw [fillMem, ih]
    · apply memmove_store_lookup_outside
      intro j hj
      rw [memmove_addr_add]
      apply ha (8 * index + j) (by omega)
      have hj' : j < 8 := by simpa only [Int.toBytes_length] using hj
      simp only [List.length_cons]
      omega
    · intro j hlo hhi
      apply ha j (by omega)
      simp only [List.length_cons]
      omega

theorem fill_bytes (m : DataMem) (src dst : BitVec 64) (data : Ssz.Bytes)
    (index capacity : Nat) (words : List (BitVec 64))
    (hs : BytesAt m src data) (hd : Disjoint src dst data.size capacity)
    (hi : 8 * (index + words.length) ≤ capacity) :
    BytesAt (fillMem m dst index words) src data := by
  induction words generalizing index m with
  | nil => exact hs
  | cons word words ih =>
    apply ih
    · exact bytes_store m src dst data capacity index word hs hd
        (by simp only [List.length_cons] at hi; omega)
    · simp only [List.length_cons] at hi
      omega

theorem fill_words (m : DataMem) (dst : BitVec 64) (index : Nat)
    (words : List (BitVec 64))
    (hb : dst.toNat + 8 * (index + words.length) ≤ 2^64) :
    ∀ i : Fin words.length,
      widthLoad (fillMem m dst index words) (dst.toNat + 8 * (index + i.val)) 8 =
        some words[i].toNat := by
  induction words generalizing index m with
  | nil => intro i; exact Fin.elim0 i
  | cons word words ih =>
    intro i
    by_cases hz : i.val = 0
    · have hi : i = ⟨0, by simp⟩ := Fin.ext hz
      subst i
      simp only [Nat.add_zero, fillMem]
      have hf : Mem.loadInt
          (fillMem (Mem.storeInt m (dst + BitVec.ofNat 64 (8 * index)) 8 word.toInt)
            dst (index + 1) words)
          (dst + BitVec.ofNat 64 (8 * index)) 8 =
          Mem.loadInt (Mem.storeInt m (dst + BitVec.ofNat 64 (8 * index)) 8 word.toInt)
            (dst + BitVec.ofNat 64 (8 * index)) 8 := by
        apply memmove_loadInt_congr
        intro j hj
        apply fill_frame
        intro k hlo hhi he
        rw [memmove_addr_add] at he
        have h := memmove_addr_injective dst (8 * (index + (word :: words).length))
          (8 * index + j) k hb (by simp; omega) (by simp at hhi ⊢; omega) he
        omega
      unfold widthLoad
      rw [width_address, hf]
      exact BoolCodec.observe_store64 m dst (8 * index) word
    · let j : Fin words.length := ⟨i.val - 1, by
        have hilen := i.isLt
        simp only [List.length_cons] at hilen
        omega⟩
      have he : index + i.val = (index + 1) + j.val := by dsimp [j]; omega
      have hw : (word :: words)[i] = words[j] := by
        have hi : i.val = j.val + 1 := by dsimp [j]; omega
        simp [hi]
      rw [hw, he]
      exact ih (m := Mem.storeInt m (dst + BitVec.ofNat 64 (8 * index)) 8 word.toInt)
        (index := index + 1) (by simp only [List.length_cons] at hb; omega) j

theorem fill_wordsAt (m : DataMem) (dst : BitVec 64) (words : List (BitVec 64))
    (hb : dst.toNat + 8 * words.length ≤ 2^64) :
    NatMemory.wordsAt (widthLoad (fillMem m dst 0 words)) dst.toNat words := by
  intro i
  simpa only [Nat.zero_add] using fill_words m dst 0 words (by simpa using hb) i

end SszX86.UintCodec.Large

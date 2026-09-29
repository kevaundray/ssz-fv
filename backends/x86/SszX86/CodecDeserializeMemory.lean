import SszX86.BoolMemory
import SszX86.CodecStorageDecode

set_option autoImplicit false

namespace SszX86.CodecDeserialize
open SszNative BoolCodec

/-- The four stores shared by successful native sequence returns. Inactive
Value fields, all enum padding, and the unused Result suffix are untouched. -/
def sequenceMem (m : DataMem) (out pointer count : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + 16) 1 4
  let m := Mem.storeInt m (out + 24) 8 pointer.toInt
  let m := Mem.storeInt m (out + 32) 8 count.toInt
  Mem.storeInt m out 8 0

/-- Unlike an enclosing output frame this is the exact write footprint. -/
def SequenceWrites (out address : BitVec 64) : Prop :=
  Codec.InSpan address out 8 ∨ Codec.InSpan address (out + 16) 1 ∨
  Codec.InSpan address (out + 24) 8 ∨ Codec.InSpan address (out + 32) 8

theorem sequence_frame (m : DataMem) (out pointer count : BitVec 64) :
    Codec.MemoryFrame m (sequenceMem m out pointer count) (SequenceWrites out) := by
  intro address outside
  have disjoint (p : BitVec 64) (n : Nat)
      (inside : ∀ a, Codec.InSpan a p n → SequenceWrites out a) :
      ∀ i < n, address ≠ p + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside (inside _ ⟨i, hi, equal⟩)
  have untouched (memory : DataMem) (p : BitVec 64) (n : Nat) (value : Int)
      (inside : ∀ a, Codec.InSpan a p n → SequenceWrites out a) :
      (Mem.storeInt memory p n value).get? address = memory.get? address := by
    apply memmove_store_lookup_outside
    intro i hi
    exact disjoint p n inside i (by simpa only [Int.toBytes_length] using hi)
  unfold sequenceMem
  rw [untouched _ out 8 0 (fun _ h => Or.inl h),
    untouched _ (out + 32) 8 count.toInt (fun _ h => Or.inr (Or.inr (Or.inr h))),
    untouched _ (out + 24) 8 pointer.toInt (fun _ h => Or.inr (Or.inr (Or.inl h))),
    untouched _ (out + 16) 1 4 (fun _ h => Or.inr (Or.inl h))]

theorem sequence_mapped (m : DataMem) (out pointer count : BitVec 64)
    (mapped : Mapped m out) : Mapped (sequenceMem m out pointer count) out := by
  unfold sequenceMem
  repeat' first | exact mapped | apply mapped_store

private theorem word_loaded (m : DataMem) (p value : BitVec 64) :
    Mem.loadInt (Mem.storeInt m p 8 value.toInt) p 8 = some (value.toNat : Int) := by
  rw [load_store_same m p 8 value.toInt (by decide)]
  have word := BitVec.ofInt_toInt (x := value)
  have numeric := congrArg BitVec.toNat word
  simp only [BitVec.toNat_ofInt] at numeric
  have positive : 0 ≤ value.toInt % 2 ^ 64 := Int.emod_nonneg _ (by decide)
  have equal : value.toInt % 2 ^ 64 = (value.toNat : Int) := by omega
  simpa only [Int.take] using congrArg some equal

/-- Observation of the active fields only; no full-record initializedness is
inferred from the compiler's later wide copies of these records. -/
theorem sequence_loads (m : DataMem) (out pointer count : BitVec 64)
    (bound : out.toNat + 80 ≤ 2 ^ 64) :
    Mem.loadInt (sequenceMem m out pointer count) out 8 = some 0 ∧
    Mem.loadInt (sequenceMem m out pointer count) (out + 16) 1 = some 4 ∧
    Mem.loadInt (sequenceMem m out pointer count) (out + 24) 8 = some (pointer.toNat : Int) ∧
    Mem.loadInt (sequenceMem m out pointer count) (out + 32) 8 = some (count.toNat : Int) := by
  have apart (memory : DataMem) (a n b k : Nat) (value : Int)
      (ha : a + n ≤ 80) (hb : b + k ≤ 80) (separate : a + n ≤ b ∨ b + k ≤ a) :=
    load_store_offset_disjoint memory out bound a n b k value ha hb separate
  constructor
  · exact load_store_same _ _ _ _ (by decide)
  constructor
  · unfold sequenceMem
    change Mem.loadInt (Mem.storeInt _ (out + BitVec.ofNat 64 0) 8 0)
      (out + BitVec.ofNat 64 16) 1 = _
    rw [apart _ 16 1 0 8 0 (by decide) (by decide) (by decide),
      apart _ 16 1 32 8 count.toInt (by decide) (by decide) (by decide),
      apart _ 16 1 24 8 pointer.toInt (by decide) (by decide) (by decide)]
    exact load_store_same _ _ _ _ (by decide)
  constructor
  · unfold sequenceMem
    change Mem.loadInt (Mem.storeInt _ (out + BitVec.ofNat 64 0) 8 0)
      (out + BitVec.ofNat 64 24) 8 = _
    rw [apart _ 24 8 0 8 0 (by decide) (by decide) (by decide),
      apart _ 24 8 32 8 count.toInt (by decide) (by decide) (by decide)]
    exact word_loaded _ _ _
  · unfold sequenceMem
    change Mem.loadInt (Mem.storeInt _ (out + BitVec.ofNat 64 0) 8 0)
      (out + BitVec.ofNat 64 32) 8 = _
    rw [apart _ 32 8 0 8 0 (by decide) (by decide) (by decide)]
    exact word_loaded _ _ _

end SszX86.CodecDeserialize

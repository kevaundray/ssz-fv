import SszX86.IndicesElementTypeOutput
import SszX86.CodecStorageBase

namespace SszX86.IndicesElementType
open UintCodec

/-- The active descriptor bytes and Result status are the only success writes. -/
def SuccessWrites (out : BitVec 64) (bytes : Nat) : Codec.Footprint := fun address =>
  Codec.InSpan address out bytes ∨ Codec.InSpan address (out + 64#64) 4

private theorem word_keep (m : DataMem) (out : BitVec 64)
    (a n b k : Nat) (value : Int)
    (ha : a + n ≤ 68) (hb : b + k ≤ 68) (apart : a + n ≤ b ∨ b + k ≤ a) :
    Mem.loadInt (Mem.storeInt m (out + BitVec.ofNat 64 b) k value)
      (out + BitVec.ofNat 64 a) n = Mem.loadInt m (out + BitVec.ofNat 64 a) n := by
  apply BoolCodec.load_store_disjoint
  intro i hi j hj equal
  simp only [memmove_addr_add] at equal
  have same := congrArg BitVec.toNat ((BitVec.add_right_inj out).mp equal)
  have ai : a + i < 2 ^ 64 := by omega
  have bj : b + j < 2 ^ 64 := by omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ai, Nat.mod_eq_of_lt bj] at same
  omega

private theorem load_zero_keep (m : DataMem) (out : BitVec 64)
    (n b k : Nat) (value : Int) (ha : n ≤ 68) (hb : b + k ≤ 68) (apart : n ≤ b) :
    Mem.loadInt (Mem.storeInt m (out + BitVec.ofNat 64 b) k value) out n =
      Mem.loadInt m out n := by
  simpa using word_keep m out 0 n b k value ha hb (Or.inl apart)

private theorem store_zero_keep (m : DataMem) (out : BitVec 64)
    (a n k : Nat) (value : Int) (ha : a + n ≤ 68) (hb : k ≤ 68) (apart : k ≤ a) :
    Mem.loadInt (Mem.storeInt m out k value) (out + BitVec.ofNat 64 a) n =
      Mem.loadInt m (out + BitVec.ofNat 64 a) n := by
  simpa using word_keep m out a n 0 k value ha hb (Or.inr apart)

private theorem stored_const (m : DataMem) (out : BitVec 64) (value : Nat)
    (small : value < 2 ^ 64) :
    Mem.loadInt (Mem.storeInt m out 8 value) out 8 = some (value : Int) := by
  rw [BoolCodec.load_store_same m out 8 value (by decide)]
  simp [Int.take, Nat.mod_eq_of_lt small]

private theorem stored_status (m : DataMem) (out : BitVec 64) (value : Nat)
    (small : value < 2 ^ 32) :
    Mem.loadInt (Mem.storeInt m out 4 value) out 4 = some (value : Int) := by
  rw [BoolCodec.load_store_same m out 4 value (by decide)]
  simp [Int.take, Nat.mod_eq_of_lt small]

theorem bool_active (m : DataMem) (out : BitVec 64) :
    Mem.loadInt (boolMem m out) out 8 = some 0 ∧
    Mem.loadInt (boolMem m out) (out + 64#64) 4 = some 0 := by
  simp (disch := decide) only [boolMem, load_zero_keep, stored_const, stored_status]

theorem uint_active (m : DataMem) (out : BitVec 64) :
    Mem.loadInt (uintMem m out) out 8 = some 1 ∧
    Mem.loadInt (uintMem m out) (out + 8#64) 8 = some 0 ∧
    Mem.loadInt (uintMem m out) (out + 16#64) 8 = some 1 ∧
    Mem.loadInt (uintMem m out) (out + 64#64) 4 = some 0 := by
  simp (disch := decide) only
    [uintMem, load_zero_keep, word_keep, stored_const, stored_status]

theorem error_active (m : DataMem) (out pointer payload : BitVec 64)
    (reason : Nat) (small : reason < 2 ^ 32) :
    Mem.loadInt (errorMem m out pointer payload reason) out 8 = some 1 ∧
    Mem.loadInt (errorMem m out pointer payload reason) (out + 8#64) 8 = some 0 ∧
    Mem.loadInt (errorMem m out pointer payload reason) (out + 16#64) 8 =
      some (pointer.toNat : Int) ∧
    Mem.loadInt (errorMem m out pointer payload reason) (out + 24#64) 8 =
      some (payload.toNat : Int) ∧
    Mem.loadInt (errorMem m out pointer payload reason) (out + 32#64) 8 = some 0 ∧
    Mem.loadInt (errorMem m out pointer payload reason) (out + 40#64) 8 = some 0 ∧
    Mem.loadInt (errorMem m out pointer payload reason) (out + 48#64) 8 = some 0 ∧
    Mem.loadInt (errorMem m out pointer payload reason) (out + 56#64) 8 = some 0 ∧
    Mem.loadInt (errorMem m out pointer payload reason) (out + 64#64) 4 = some (reason : Int) := by
  simp (disch := first | exact small | decide) only
    [errorMem, load_zero_keep, word_keep, CodecPlanSingleton.stored_word,
      stored_const, stored_status]

theorem copy_active (m : DataMem) (out : BitVec 64) (words : DescWords) :
    words.At (copyMem m out words) out ∧
    Mem.loadInt (copyMem m out words) (out + 64#64) 4 = some 0 := by
  simp (disch := decide) only
    [DescWords.At, copyMem, load_zero_keep, store_zero_keep, word_keep,
      CodecPlanSingleton.stored_word, stored_status]

private theorem success_store_frame (m : DataMem) (out : BitVec 64)
    (bytes offset width : Nat) (value : Int) (bound : offset + width ≤ bytes) :
    Codec.MemoryFrame m (Mem.storeInt m (out + BitVec.ofNat 64 offset) width value)
      (SuccessWrites out bytes) := by
  intro address outside
  apply BoolCodec.store_frame (limit := bytes)
  · exact bound
  · intro i inside equal
    exact outside (Or.inl ⟨i, inside, equal⟩)

private theorem status_store_frame (m : DataMem) (out : BitVec 64)
    (bytes : Nat) (value : Int) :
    Codec.MemoryFrame m (Mem.storeInt m (out + 64#64) 4 value)
      (SuccessWrites out bytes) := by
  intro address outside
  apply memmove_store_lookup_outside
  intro i inside equal
  exact outside (Or.inr ⟨i, by simpa only [Int.toBytes_length] using inside, equal⟩)

private theorem frame_trans {m n o : DataMem} {writes : Codec.Footprint}
    (first : Codec.MemoryFrame m n writes) (second : Codec.MemoryFrame n o writes) :
    Codec.MemoryFrame m o writes := by
  intro address outside
  exact (second address outside).trans (first address outside)

theorem bool_frame (m : DataMem) (out : BitVec 64) :
    Codec.MemoryFrame m (boolMem m out) (SuccessWrites out 8) := by
  unfold boolMem
  apply frame_trans ?_ (status_store_frame _ out 8 0)
  simpa using success_store_frame m out 8 0 8 0 (by decide)

theorem uint_frame (m : DataMem) (out : BitVec 64) :
    Codec.MemoryFrame m (uintMem m out) (SuccessWrites out 24) := by
  unfold uintMem
  apply frame_trans ?_ (status_store_frame _ out 24 0)
  apply frame_trans ?_ (success_store_frame _ out 24 16 8 1 (by decide))
  apply frame_trans ?_ (success_store_frame _ out 24 8 8 0 (by decide))
  simpa using success_store_frame m out 24 0 8 1 (by decide)

theorem copy_frame (m : DataMem) (out : BitVec 64) (words : DescWords) :
    Codec.MemoryFrame m (copyMem m out words) (SuccessWrites out 40) := by
  unfold copyMem
  apply frame_trans ?_ (status_store_frame _ out 40 0)
  have head := success_store_frame _ out 40 0 8 words.tag.toInt (by decide)
  simp only [BitVec.ofNat_zero, BitVec.add_zero] at head
  apply frame_trans ?_ head
  apply frame_trans ?_ (success_store_frame _ out 40 8 8 words.word8.toInt (by decide))
  apply frame_trans ?_ (success_store_frame _ out 40 16 8 words.word16.toInt (by decide))
  apply frame_trans ?_ (success_store_frame _ out 40 24 8 words.word24.toInt (by decide))
  exact success_store_frame _ out 40 32 8 words.word32.toInt (by decide)

theorem error_frame (m : DataMem) (out pointer payload : BitVec 64) (reason : Int) :
    Codec.MemoryFrame m (errorMem m out pointer payload reason) (SuccessWrites out 64) := by
  unfold errorMem
  apply frame_trans ?_ (status_store_frame _ out 64 reason)
  apply frame_trans ?_ (success_store_frame _ out 64 56 8 0 (by decide))
  apply frame_trans ?_ (success_store_frame _ out 64 48 8 0 (by decide))
  apply frame_trans ?_ (success_store_frame _ out 64 40 8 0 (by decide))
  apply frame_trans ?_ (success_store_frame _ out 64 32 8 0 (by decide))
  apply frame_trans ?_ (success_store_frame _ out 64 24 8 payload.toInt (by decide))
  apply frame_trans ?_ (success_store_frame _ out 64 16 8 pointer.toInt (by decide))
  apply frame_trans ?_ (success_store_frame _ out 64 8 8 0 (by decide))
  simpa using success_store_frame m out 64 0 8 1 (by decide)

/-- Caller return ownership is transported through the actual output frame;
no post-store memory observation is assumed by an original-entry contract. -/
theorem retained_return (m n : DataMem) (out sp ra : BitVec 64) (bytes : Nat)
    (frame : Codec.MemoryFrame m n (SuccessWrites out bytes))
    (separate : ∀ i < 8, ¬ SuccessWrites out bytes (sp + BitVec.ofNat 64 i))
    (ret : Mem.loadInt m sp 8 = some (Int.ofBytes (wordBytes ra))) :
    Mem.loadInt n sp 8 = some (Int.ofBytes (wordBytes ra)) := by
  rw [Emit.frame_load m n (SuccessWrites out bytes) frame sp 8 separate]
  exact ret

end SszX86.IndicesElementType

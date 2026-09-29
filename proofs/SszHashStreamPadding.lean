import Ssz.Hash.Sha256
import Init.Data.ByteArray.Lemmas
import Init.Data.Array.OfFn
import Init.Data.UInt.Lemmas
import Init.Omega

namespace SszNative.HashStream

/-- Padding depends only on the position in the current block. -/
theorem paddingZeros_mod (n : Nat) :
    Ssz.Sha256.paddingZeros n = Ssz.Sha256.paddingZeros (n % 64) := by
  simp [Ssz.Sha256.paddingZeros, Nat.add_mod]

theorem paddingZeros_eq (n : Nat) :
    Ssz.Sha256.paddingZeros n =
      if n % 64 < 56 then 55 - n % 64 else 119 - n % 64 := by
  rw [paddingZeros_mod]
  unfold Ssz.Sha256.paddingZeros
  split <;> omega

theorem paddingZeros_of_lt (r : Nat) (h : r < 56) :
    Ssz.Sha256.paddingZeros r = 55 - r := by
  rw [paddingZeros_eq, Nat.mod_eq_of_lt (by omega)]
  simp only [h, ↓reduceIte]

theorem paddingZeros_of_ge (r : Nat) (h : 56 ≤ r) (hr : r < 64) :
    Ssz.Sha256.paddingZeros r = 119 - r := by
  rw [paddingZeros_eq, Nat.mod_eq_of_lt hr]
  simp only [show ¬ r < 56 by omega, ↓reduceIte]

/-- Big-endian bytes of the native, wrapping bit counter. -/
def finalLengthBytes (byteLen : UInt64) : List UInt8 :=
  (Array.ofFn fun i : Fin 8 =>
    ((byteLen * 8) >>> (56 - 8 * UInt64.ofNat i.val)).toUInt8).toList

@[simp] theorem finalLengthBytes_length (byteLen : UInt64) :
    (finalLengthBytes byteLen).length = 8 := by
  simp [finalLengthBytes]

/-- No upper bound on the logical byte length is needed. -/
theorem finalLengthBytes_ofNat (n : Nat) :
    finalLengthBytes (UInt64.ofNat n) = (Ssz.Sha256.lengthBytes n).data.toList := rfl

theorem wrapped_count_add (m n : Nat) :
    UInt64.ofNat m + UInt64.ofNat n = UInt64.ofNat (m + n) :=
  (UInt64.ofNat_add m n).symm

theorem wrapped_count_mul8 (n : Nat) :
    UInt64.ofNat n * 8 = UInt64.ofNat (n * 8) := by
  simp

theorem wrapped_bit_count (n : Nat) :
    (UInt64.ofNat n * 8).toNat = (n * 8) % 2 ^ 64 := by
  rw [wrapped_count_mul8]
  rfl

theorem finalLengthBytes_add (m n : Nat) :
    finalLengthBytes (UInt64.ofNat m + UInt64.ofNat n) =
      (Ssz.Sha256.lengthBytes (m + n)).data.toList := by
  rw [wrapped_count_add, finalLengthBytes_ofNat]

@[simp] theorem lengthBytes_size (n : Nat) :
    (Ssz.Sha256.lengthBytes n).size = 8 := by
  simp [Ssz.Sha256.lengthBytes, ByteArray.size]

/-- The entire final one or two blocks, including the uncompressed residual. -/
def residualPad (xs : List UInt8) (byteLen : UInt64) : List UInt8 :=
  xs ++ [0x80] ++
    List.replicate (if xs.length < 56 then 55 - xs.length else 119 - xs.length) 0 ++
    finalLengthBytes byteLen

theorem residualPad_one (xs : List UInt8) (byteLen : UInt64) (h : xs.length < 56) :
    residualPad xs byteLen =
      xs ++ [0x80] ++ List.replicate (55 - xs.length) 0 ++ finalLengthBytes byteLen := by
  simp only [residualPad, h, ↓reduceIte]

/-- The first block fills the current buffer; the second starts with 56 zeros. -/
theorem residualPad_two (xs : List UInt8) (byteLen : UInt64)
    (h : 56 ≤ xs.length) (hr : xs.length < 64) :
    residualPad xs byteLen =
      (xs ++ [0x80] ++ List.replicate (63 - xs.length) 0) ++
      (List.replicate 56 0 ++ finalLengthBytes byteLen) := by
  have hz : 119 - xs.length = (63 - xs.length) + 56 := by omega
  simp only [residualPad, show ¬ xs.length < 56 by omega, ↓reduceIte, hz,
    ← List.replicate_append_replicate, List.append_assoc]

theorem residualPad_one_length (xs : List UInt8) (byteLen : UInt64)
    (h : xs.length < 56) : (residualPad xs byteLen).length = 64 := by
  rw [residualPad_one xs byteLen h]
  simp only [List.length_append, List.length_cons, List.length_nil,
    List.length_replicate, finalLengthBytes_length]
  omega

theorem residualPad_two_first_length (xs : List UInt8) (hr : xs.length < 64) :
    (xs ++ [0x80] ++ List.replicate (63 - xs.length) 0).length = 64 := by
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  omega

theorem residualPad_two_last_length (byteLen : UInt64) :
    (List.replicate 56 0 ++ finalLengthBytes byteLen).length = 64 := by
  simp

theorem residualPad_two_length (xs : List UInt8) (byteLen : UInt64)
    (h : 56 ≤ xs.length) (hr : xs.length < 64) :
    (residualPad xs byteLen).length = 128 := by
  rw [residualPad_two xs byteLen h hr, List.length_append,
    residualPad_two_first_length xs hr, residualPad_two_last_length]

theorem residualPad_length (xs : List UInt8) (byteLen : UInt64)
    (hr : xs.length < 64) :
    (residualPad xs byteLen).length = if xs.length < 56 then 64 else 128 := by
  split
  · exact residualPad_one_length xs byteLen ‹_›
  · exact residualPad_two_length xs byteLen (by omega) hr

/-- The Rust test after writing the delimiter is precisely the 56-byte split. -/
theorem finalization_split (r : Nat) : (56 < r + 1) ↔ 56 ≤ r := by omega

theorem pad_toList (message : ByteArray) :
    (Ssz.Sha256.pad message).data.toList =
      message.data.toList ++ [0x80] ++
        List.replicate (Ssz.Sha256.paddingZeros message.size) 0 ++
        (Ssz.Sha256.lengthBytes message.size).data.toList := by
  simp [Ssz.Sha256.pad]

/-- A split at the last completed block refines the pinned padding exactly. -/
theorem pad_toList_split (message : ByteArray) (done xs : List UInt8)
    (hsplit : message.data.toList = done ++ xs)
    (hres : xs.length = message.size % 64) :
    (Ssz.Sha256.pad message).data.toList =
      done ++ residualPad xs (UInt64.ofNat message.size) := by
  rw [pad_toList, hsplit, paddingZeros_eq]
  simp only [residualPad, hres, finalLengthBytes_ofNat, List.append_assoc]

/-- Equivalent formulation using only the completed-prefix and residual bounds. -/
theorem pad_toList_split_of_aligned (message : ByteArray) (done xs : List UInt8)
    (hsplit : message.data.toList = done ++ xs)
    (haligned : done.length % 64 = 0) (hres : xs.length < 64) :
    (Ssz.Sha256.pad message).data.toList =
      done ++ residualPad xs (UInt64.ofNat message.size) := by
  apply pad_toList_split message done xs hsplit
  have hlen := congrArg List.length hsplit
  simp only [List.length_append, Array.length_toList] at hlen
  change message.size = done.length + xs.length at hlen
  omega

/-- Canonical last-block residual, with no restriction on total logical size. -/
theorem pad_toList_take_drop (message : ByteArray) :
    (Ssz.Sha256.pad message).data.toList =
      message.data.toList.take (message.size - message.size % 64) ++
        residualPad (message.data.toList.drop (message.size - message.size % 64))
          (UInt64.ofNat message.size) := by
  apply pad_toList_split
  · exact (List.take_append_drop _ _).symm
  · simp only [List.length_drop, Array.length_toList]
    change message.size - (message.size - message.size % 64) = message.size % 64
    omega

/-- The same decomposition can be instantiated directly with semantic byte lists. -/
theorem pad_list_split (done xs : List UInt8)
    (haligned : done.length % 64 = 0) (hres : xs.length < 64) :
    (Ssz.Sha256.pad ⟨(done ++ xs).toArray⟩).data.toList =
      done ++ residualPad xs (UInt64.ofNat (done.length + xs.length)) := by
  simpa [ByteArray.size] using
    pad_toList_split_of_aligned ⟨(done ++ xs).toArray⟩ done xs (by simp) haligned hres

@[simp] theorem digest_size (state : Vector UInt32 8) :
    (Ssz.Sha256.digest state).size = 32 := by
  simp [Ssz.Sha256.digest, ByteArray.size]

@[simp] theorem digest_toList_length (state : Vector UInt32 8) :
    (Ssz.Sha256.digest state).data.toList.length = 32 := by
  change (Ssz.Sha256.digest state).size = 32
  exact digest_size state

@[simp] theorem hash_size (message : ByteArray) :
    (Ssz.Sha256.hash message).size = 32 := by
  unfold Ssz.Sha256.hash
  exact digest_size _

end SszNative.HashStream

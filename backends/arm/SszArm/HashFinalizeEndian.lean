import SszArm.HashStoreMemory
import Init.Data.UInt.Bitwise

namespace SszArm.Hash.Finalize

/-- Scalar form of the exact REV X instruction, without touching a machine state. -/
def reverse64 (x : BitVec 64) : BitVec 64 := rev_elems 64 8 x (by decide) (by decide)

/-- Scalar form of the exact REV W instruction. -/
def reverse32 (x : BitVec 32) : BitVec 32 := rev_elems 32 8 x (by decide) (by decide)

theorem reverse64_byte (x : BitVec 64) (i : Fin 8) :
    (reverse64 x).extractLsByte i.val = (x >>> (56 - 8 * i.val)).setWidth 8 := by
  rcases i with ⟨i, hi⟩
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    apply BitVec.eq_of_getLsbD_eq
    intro bit bound
    simp (config := {decide := true}) only
      [reverse64, rev_elems, BitVec.extractLsByte, Nat.reduceSub,
       Nat.reduceMul, ↓reduceDIte, BitVec.cast_eq]
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_cast,
      BitVec.getLsbD_setWidth, Nat.reduceAdd, Nat.zero_add, bound, decide_true,
      Bool.true_and]
    repeat rw [BitVec.getLsbD_append]
    simp (disch := omega) only [BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ushiftRight, if_pos, if_neg, decide_eq_true, decide_eq_false,
      Bool.true_and, Bool.false_and, Nat.add_sub_cancel_left, Nat.add_sub_cancel,
      ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add]
  | i + 8, hi => omega

theorem reverse32_byte (x : BitVec 32) (i : Fin 4) :
    (reverse32 x).extractLsByte i.val = (x >>> (24 - 8 * i.val)).setWidth 8 := by
  rcases i with ⟨i, hi⟩
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ =>
    apply BitVec.eq_of_getLsbD_eq
    intro bit bound
    simp (config := {decide := true}) only
      [reverse32, rev_elems, BitVec.extractLsByte, Nat.reduceSub,
       Nat.reduceMul, ↓reduceDIte, BitVec.cast_eq]
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_cast,
      BitVec.getLsbD_setWidth, Nat.reduceAdd, Nat.zero_add, bound, decide_true,
      Bool.true_and]
    repeat rw [BitVec.getLsbD_append]
    simp (disch := omega) only [BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ushiftRight, if_pos, if_neg, decide_eq_true, decide_eq_false,
      Bool.true_and, Bool.false_and, Nat.add_sub_cancel_left, Nat.add_sub_cancel,
      ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add]
  | i + 4, hi => omega

theorem shift3_modular (x : BitVec 64) : x <<< (3 : Nat) = x * 8#64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_mul, Nat.shiftLeft_eq]

/-- This is UInt64 multiplication, so the bit count wraps before byte extraction. -/
theorem length_encoding (byteLen : UInt64) (i : Fin 8) :
    (reverse64 (byteLen.toBitVec <<< (3 : Nat))).extractLsByte i.val =
      (SszNative.HashStream.finalLengthBytes byteLen)[i.val].toBitVec := by
  rw [reverse64_byte, shift3_modular]
  rcases i with ⟨i, hi⟩
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp (config := {decide := true}) [SszNative.HashStream.finalLengthBytes,
      UInt64.toBitVec_shiftRight, UInt64.toBitVec_toUInt8, UInt64.toBitVec_mul,
      BitVec.setWidth_mul byteLen.toBitVec 8#64 (show 8 ≤ 64 by decide)]
  | i + 8, hi => omega

private theorem write_mem_bytes_eight (count : Nat) (size : count = 8)
    (s : ArmState) (address : BitVec 64) (value : BitVec 64) :
    write_mem_bytes count address (value.setWidth (count * 8)) s =
      write_mem_bytes 8 address value s := by
  subst count
  simp only [BitVec.setWidth_eq]

private theorem extractLsByte_setWidth_eight (count : Nat) (size : count = 8)
    (value : BitVec 64) (i : Nat) :
    (value.setWidth (count * 8)).extractLsByte i = value.extractLsByte i := by
  subst count
  simp only [BitVec.setWidth_eq]

/-- The eight-byte STR is exactly the source's final overwrite at offset 56. -/
theorem length_store (s : ArmState) (address : BitVec 64) (buf : Vector UInt8 64)
    (byteLen : UInt64) (physical : address.toNat + 64 ≤ 2^64)
    (source : BytesAt s address ⟨buf.toArray⟩) :
    BytesAt (write_mem_bytes 8 (address + 56#64)
      (reverse64 (byteLen.toBitVec <<< (3 : Nat))) s) address
      ⟨(SszNative.HashStream.overwrite buf 56
        (SszNative.HashStream.finalLengthBytes byteLen) (by simp)).toArray⟩ := by
  have stored := bytesAt_store s address buf 56
    (SszNative.HashStream.finalLengthBytes byteLen) (by simp)
    ((reverse64 (byteLen.toBitVec <<< (3 : Nat))).setWidth
      ((SszNative.HashStream.finalLengthBytes byteLen).length * 8))
    (fun i => by
      rw [extractLsByte_setWidth_eight _
        (SszNative.HashStream.finalLengthBytes_length byteLen)]
      exact length_encoding byteLen ⟨i.val, by simpa using i.isLt⟩)
    physical source
  rw [write_mem_bytes_eight _ (SszNative.HashStream.finalLengthBytes_length byteLen)] at stored
  exact stored

/-- Each digest byte is selected from the original, unreversed chaining word. -/
theorem digest_byte (words : Vector UInt32 8) (i : Fin 32) :
    ((Ssz.Sha256.digest words)[i.val]'(by
      simpa only [SszNative.HashStream.digest_size] using i.isLt)).toBitVec =
      (reverse32 words[i.val / 4].toBitVec).extractLsByte (i.val % 4) := by
  rw [reverse32_byte _ ⟨i.val % 4, by omega⟩]
  simp only [Ssz.Sha256.digest, ByteArray.getElem_eq_getElem_data, Array.getElem_ofFn]
  have rem : i.val % 4 = 0 ∨ i.val % 4 = 1 ∨ i.val % 4 = 2 ∨ i.val % 4 = 3 := by omega
  rcases rem with rem | rem | rem | rem <;>
    simp (config := {decide := true}) [rem, UInt32.toBitVec_shiftRight,
      UInt32.toBitVec_toUInt8]

end SszArm.Hash.Finalize

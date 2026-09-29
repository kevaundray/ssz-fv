import SszX86.HashFinalizeTail
import SszX86.HashMemoryFacts
import Init.Data.UInt.Bitwise

namespace SszX86.Hash
open SszNative.HashStream

/-- Shared layout bytes are the low byte of the corresponding logical shift. -/
theorem littleByte_toBitVec {w : Nat} (value : BitVec w) (lane : Nat) :
    (littleByte value.toNat lane).toBitVec = (value >>> (8 * lane)).setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  have power : 2 ^ (8 * lane) = 256 ^ lane := by
    rw [show (256 : Nat) = 2 ^ 8 by decide, Nat.pow_mul]
  simp [littleByte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, power]

/-- Signed dword stores retain the exact unsigned source bytes. -/
theorem dword_store_byte (value : BitVec 32) (i : Nat) (hi : i < 4) :
    (Int.toBytes 4 value.toInt)[i]? = some (littleByte value.toNat i) := by
  have unsigned : value.toInt.take 32 = Int.ofNat value.toNat := by
    have bound := value.isLt
    change value.toInt % 4294967296 = (value.toNat : Int)
    rw [BitVec.toInt_eq_toNat_cond]
    split <;> omega
  have equal : Int.toBytes 4 value.toInt = Int.toBytes 4 (Int.ofNat value.toNat) := by
    rw [← unsigned]
    exact (Int.toBytes_emod 4 value.toInt).symm
  rw [equal]
  exact scalar_byte 4 value.toNat i hi

theorem stored_qword_byte (value : BitVec 64) (i : Fin 8) :
    ((Int.toBytes 8 value.toInt)[i.val]'(by simp; exact i.isLt)).toBitVec =
      (value >>> (8 * i.val)).setWidth 8 := by
  have h := word_store_byte value i.val i.isLt
  rw [List.getElem?_eq_getElem (by simp; exact i.isLt)] at h
  rw [Option.some.inj h, littleByte_toBitVec]

theorem stored_dword_byte (value : BitVec 32) (i : Fin 4) :
    ((Int.toBytes 4 value.toInt)[i.val]'(by simp; exact i.isLt)).toBitVec =
      (value >>> (8 * i.val)).setWidth 8 := by
  have h := dword_store_byte value i.val i.isLt
  rw [List.getElem?_eq_getElem (by simp; exact i.isLt)] at h
  rw [Option.some.inj h, littleByte_toBitVec]

namespace Finalize

/-- Each byte of the actual BSWAP QWORD is selected from the opposite source lane. -/
theorem swap64_byte (value : BitVec 64) (i : Fin 8) :
    ((swap64 value) >>> (8 * i.val)).setWidth 8 =
      (value >>> (56 - 8 * i.val)).setWidth 8 := by
  rcases i with ⟨i, hi⟩
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    apply BitVec.eq_of_getLsbD_eq
    intro bit bound
    simp (disch := omega) [swap64, BitVec.getLsbD_append, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', BitVec.getLsbD_cast]
  | i + 8, hi => omega

/-- The dword BSWAP does not pull bytes from the old high register half. -/
theorem swap32_byte (value : BitVec 32) (i : Fin 4) :
    ((swap32 value) >>> (8 * i.val)).setWidth 8 =
      (value >>> (24 - 8 * i.val)).setWidth 8 := by
  rcases i with ⟨i, hi⟩
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ =>
    apply BitVec.eq_of_getLsbD_eq
    intro bit bound
    simp (disch := omega) [swap32, BitVec.getLsbD_append, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', BitVec.getLsbD_cast]
  | i + 4, hi => omega

theorem shift3_modular (value : BitVec 64) : value <<< (3 : Nat) = value * 8#64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_mul, Nat.shiftLeft_eq]

/-- The actual SHL; BSWAP; MOV sequence writes the wrapped source bit length. -/
theorem length_store_bytes (byteLen : UInt64) :
    Int.toBytes 8 (swap64 (byteLen.toBitVec <<< (3 : Nat))).toInt =
      finalLengthBytes byteLen := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have bound : i < 8 := by simpa only [Int.toBytes_length] using hi
    apply UInt8.toBitVec_inj.mp
    rw [stored_qword_byte _ ⟨i, bound⟩, swap64_byte, shift3_modular]
    match i, bound with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
      simp [finalLengthBytes, UInt64.toBitVec_shiftRight,
        UInt64.toBitVec_toUInt8, UInt64.toBitVec_mul]
    | i + 8, bound => omega

/-- Each of the eight MOVL stores agrees with the pinned digest's byte selector. -/
theorem digest_store_byte (words : Vector UInt32 8) (wordIndex : Fin 8) (lane : Fin 4) :
    (Int.toBytes 4 (swap32 words[wordIndex.val].toBitVec).toInt)[lane.val]?
      = (Ssz.Sha256.digest words).data.toList[4 * wordIndex.val + lane.val]? := by
  have length : 4 * wordIndex.val + lane.val < 32 := by omega
  rw [List.getElem?_eq_getElem (by simp; exact lane.isLt),
    List.getElem?_eq_getElem (by simpa [Ssz.Sha256.digest] using length)]
  congr 1
  apply UInt8.toBitVec_inj.mp
  rw [stored_dword_byte _ lane, swap32_byte]
  have div : (4 * wordIndex.val + lane.val) / 4 = wordIndex.val := by omega
  have mod : (4 * wordIndex.val + lane.val) % 4 = lane.val := by omega
  rcases lane with ⟨lane, bound⟩
  match lane, bound with
  | 0, _ | 1, _ | 2, _ | 3, _ =>
    simp [Ssz.Sha256.digest, div, mod, UInt32.toBitVec_shiftRight,
      UInt32.toBitVec_toUInt8]
  | lane + 4, bound => omega

end Finalize
end SszX86.Hash

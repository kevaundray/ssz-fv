import SszX86.CodecDecodeOffsetsExec
import SszX86.UintLimbMemory
import SszCodecDecode

set_option autoImplicit false

namespace SszX86.CodecDecodeOffsets
open SszNative UintCodec

private theorem append_nat {leftWidth rightWidth : Nat}
    (left : BitVec leftWidth) (right : BitVec rightWidth) :
    (left ++ right).toNat = left.toNat * 2 ^ rightWidth + right.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt right.isLt,
    Nat.shiftLeft_eq]

theorem word_value (b0 b1 b2 b3 : BitVec 8) :
    (CodecReadOffset.value b0 b1 b2 b3).toNat =
      b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) := by
  have h0 := b0.isLt
  have h1 := b1.isLt
  have h2 := b2.isLt
  have h3 := b3.isLt
  simp only [CodecReadOffset.value, BitVec.toNat_setWidth, append_nat]
  change (((b3.toNat * 256 + b2.toNat) * 256 + b1.toNat) * 256 + b0.toNat) %
      18446744073709551616 = _
  omega

def inputByte (data : Ssz.Bytes) (start offset : Nat) : BitVec 8 :=
  (data[start + offset]?.getD 0).toBitVec

def inputWord (data : Ssz.Bytes) (index : Nat) : BitVec 64 :=
  CodecReadOffset.value (inputByte data (4 * index) 0) (inputByte data (4 * index) 1)
    (inputByte data (4 * index) 2) (inputByte data (4 * index) 3)

/-- The very bytes read by the four native MOVZX instructions are the existing
shared little-endian offset word, not a parallel table interpretation. -/
theorem inputWord_shared (data : Ssz.Bytes) (index : Nat) :
    (inputWord data index).toNat = Ssz.readUint data (index * Ssz.bytesPerOffset) Ssz.bytesPerOffset := by
  rw [inputWord, word_value]
  simp [inputByte, Ssz.readUint, Ssz.bytesPerOffset, Nat.mul_comm, Nat.add_assoc]

theorem inputWord_bytes (m : DataMem) (source : BitVec 64) (data : Ssz.Bytes)
    (stored : Large.BytesAt m source data) (index : Nat) (bound : 4 * index + 4 ≤ data.size) :
    CodecReadOffset.BytesAt m (source + BitVec.ofNat 64 (4 * index))
      (inputByte data (4 * index) 0) (inputByte data (4 * index) 1)
      (inputByte data (4 * index) 2) (inputByte data (4 * index) 3) := by
  have byte (offset : Nat) (small : offset < 4) := stored (4 * index + offset) (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [inputByte, Nat.add_zero, UInt8.toNat_toBitVec] using byte 0 (by decide)
  · simpa only [inputByte, BitVec.ofNat_add, BitVec.add_assoc, UInt8.toNat_toBitVec]
      using byte 1 (by decide)
  · simpa only [inputByte, BitVec.ofNat_add, BitVec.add_assoc, UInt8.toNat_toBitVec]
      using byte 2 (by decide)
  · simpa only [inputByte, BitVec.ofNat_add, BitVec.add_assoc, UInt8.toNat_toBitVec]
      using byte 3 (by decide)

/-- The four unusual precomputed native bounds correspond to bytes one through
four of the next table entry. Physical table extent excludes each panic edge. -/
theorem quota_gt (scope index displacement : Nat)
    (byte : 1 ≤ displacement ∧ displacement ≤ 4)
    (fits : 4 * (index + 2) ≤ scope) :
    index < (scope - displacement) / 4 := by
  omega

theorem quota_register (scope : BitVec 64) (index displacement : Nat)
    (byte : 1 ≤ displacement ∧ displacement ≤ 4)
    (fits : 4 * (index + 2) ≤ scope.toNat) :
    (scope - BitVec.ofNat 64 displacement) >>> 2 ≠ BitVec.ofNat 64 index := by
  have scopeBound := scope.isLt
  have indexBound : index < 2 ^ 64 := by omega
  have displacementBound : displacement < 2 ^ 64 := by omega
  have displacementNat : (BitVec.ofNat 64 displacement).toNat = displacement :=
    Nat.mod_eq_of_lt displacementBound
  have difference : (scope - BitVec.ofNat 64 displacement).toNat = scope.toNat - displacement := by
    rw [BitVec.toNat_sub_of_le (by rw [displacementNat]; omega), displacementNat]
  have shifted : ((scope - BitVec.ofNat 64 displacement) >>> 2).toNat =
      (scope.toNat - displacement) / 4 := by
    rw [BitVec.toNat_ushiftRight, difference, Nat.shiftRight_eq_div_pow]
  intro equal
  have numbers := congrArg BitVec.toNat equal
  rw [shifted, BitVec.toNat_ofNat, Nat.mod_eq_of_lt indexBound] at numbers
  have greater := quota_gt scope.toNat index displacement byte fits
  omega

end SszX86.CodecDecodeOffsets

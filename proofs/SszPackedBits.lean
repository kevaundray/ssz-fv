import SszPacking

/-! Native packed-bit correspondence for SSZ bitfield encodings. -/

namespace SszNative.PackedBits

open Ssz SszNative.Packing

/-- Packed bytes with high padding removed from the last byte when the bit count is not aligned. -/
def canonicalBytes (src : Bytes) (n : Nat) : Bytes :=
  src.extract 0 (n / 8) ++
    (if n % 8 = 0 then #[] else #[src[n / 8]! &&& UInt8.ofNat (2 ^ (n % 8) - 1)])

/-- Packed bytes with the SSZ delimiter bit added after the data bits. -/
def delimitedBytes (src : Bytes) (n : Nat) : Bytes :=
  src.extract 0 (n / 8) ++
    #[if n % 8 = 0 then (1 : UInt8) else (src[n / 8]! &&& UInt8.ofNat (2 ^ (n % 8) - 1)) |||
      (1 <<< UInt8.ofNat (n % 8))]

set_option maxRecDepth 4096 in
private theorem byte_bit (byte : UInt8) (offset : Fin 8) :
    ((byte >>> UInt8.ofNat offset.val) &&& 1 == 1) = byte.toBitVec.getLsbD offset.val := by
  cases byte with
  | ofBitVec byte =>
    cases byte with
    | ofFin byte =>
      revert byte offset
      decide

private theorem byte_eq_of_bits {left right : UInt8}
    (same : ∀ offset, offset < 8 →
      ((left >>> UInt8.ofNat offset) &&& 1 == 1) =
      ((right >>> UInt8.ofNat offset) &&& 1 == 1)) : left = right := by
  apply UInt8.eq_iff_toBitVec_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro offset small
  simpa only [byte_bit left ⟨offset, small⟩, byte_bit right ⟨offset, small⟩] using
    same offset small

private theorem unpacked_bit (src : Bytes) (n k : Nat) :
    (unpackBits src n)[k]?.getD false =
      if k < n then (src[k / 8]! >>> UInt8.ofNat (k % 8)) &&& 1 == 1 else false := by
  by_cases h : k < n
  · rw [Array.getElem?_eq_getElem (by simpa using h), Option.getD_some]
    simp [unpackBits, h]
  · rw [Array.getElem?_eq_none (by simpa using Nat.le_of_not_lt h)]
    simp [h]

private theorem pushed_bit (bits : Array Bool) (k : Nat) :
    (bits.push true)[k]?.getD false =
      if k = bits.size then true else bits[k]?.getD false := by
  by_cases h : k = bits.size <;> simp [Array.getElem?_push, h]

private theorem packByte_push_prefix (bits : Array Bool) (byteIndex : Nat)
    (h : byteIndex * 8 + 7 < bits.size) :
    packByte (bits.push true) byteIndex = packByte bits byteIndex := by
  apply byte_eq_of_bits
  intro offset small
  rw [packByte_bit _ _ _ small, packByte_bit _ _ _ small, pushed_bit]
  have hne : byteIndex * 8 + offset ≠ bits.size := by omega
  simp [hne]

private theorem packed_prefix_byte (src : Bytes) (n i : Nat) (hi : i < n / 8) :
    packByte (unpackBits src n) i = src[i]! := by
  apply byte_eq_of_bits
  intro offset small
  rw [packByte_bit _ _ _ small, unpacked_bit]
  have hdiv : (i * 8 + offset) / 8 = i := by omega
  have hmod : (i * 8 + offset) % 8 = offset := by omega
  have hpos : i * 8 + offset < n := by omega
  simp only [hdiv, hmod, hpos, ↓reduceIte]

set_option maxRecDepth 4096 in
private theorem canonical_tail_spec (byte : UInt8) (r : Fin 8) (offset : Fin 8) :
    (((byte &&& UInt8.ofNat (2 ^ r.val - 1)) >>> UInt8.ofNat offset.val) &&& 1 == 1) =
      if offset.val < r.val then ((byte >>> UInt8.ofNat offset.val) &&& 1 == 1) else false := by
  cases byte with
  | ofBitVec byte =>
    cases byte with
    | ofFin byte =>
      revert byte r offset
      decide

set_option maxRecDepth 4096 in
private theorem delimited_tail_spec (byte : UInt8) (r : Fin 8) (offset : Fin 8) :
    ((((byte &&& UInt8.ofNat (2 ^ r.val - 1)) ||| (1 <<< UInt8.ofNat r.val)) >>>
      UInt8.ofNat offset.val) &&& 1 == 1) =
      if offset.val < r.val then ((byte >>> UInt8.ofNat offset.val) &&& 1 == 1)
      else if offset.val = r.val then true else false := by
  cases byte with
  | ofBitVec byte =>
    cases byte with
    | ofFin byte =>
      revert byte r offset
      decide

private theorem canonical_tail_byte (src : Bytes) (n : Nat) :
    packByte (unpackBits src n) (n / 8) =
      src[n / 8]! &&& UInt8.ofNat (2 ^ (n % 8) - 1) := by
  apply byte_eq_of_bits
  intro offset small
  rw [packByte_bit _ _ _ small, unpacked_bit,
    canonical_tail_spec _ ⟨n % 8, by omega⟩ ⟨offset, small⟩]
  have hdiv : (n / 8 * 8 + offset) / 8 = n / 8 := by omega
  have hmod : (n / 8 * 8 + offset) % 8 = offset := by omega
  have hpos : (n / 8 * 8 + offset < n) ↔ offset < n % 8 := by omega
  simp only [hdiv, hmod, hpos]

private theorem delimited_tail_byte (src : Bytes) (n : Nat) :
    packByte ((unpackBits src n).push true) (n / 8) =
      (src[n / 8]! &&& UInt8.ofNat (2 ^ (n % 8) - 1)) |||
        (1 <<< UInt8.ofNat (n % 8)) := by
  apply byte_eq_of_bits
  intro offset small
  rw [packByte_bit _ _ _ small, pushed_bit, unpackBits_size, unpacked_bit,
    delimited_tail_spec _ ⟨n % 8, by omega⟩ ⟨offset, small⟩]
  have hdiv : (n / 8 * 8 + offset) / 8 = n / 8 := by omega
  have hmod : (n / 8 * 8 + offset) % 8 = offset := by omega
  have hpos : (n / 8 * 8 + offset < n) ↔ offset < n % 8 := by omega
  have heq : (n / 8 * 8 + offset = n) ↔ offset = n % 8 := by omega
  simp only [hdiv, hmod, hpos, heq]
  by_cases h : offset < n % 8
  · simp [h, show offset ≠ n % 8 by omega]
  · simp [h]

/-- Packing unpacked bits reproduces the native bulk prefix and masked tail,
including empty inputs and arbitrary dirty input padding. -/
theorem packBits_unpackBits_canonicalBytes (src : Bytes) (n : Nat)
    (hsrc : src.size = (n + 7) / 8) :
    packBits (unpackBits src n) ((n + 7) / 8) = canonicalBytes src n := by
  have hfloor : n / 8 ≤ src.size := by omega
  have hs : (src.extract 0 (n / 8)).size = n / 8 := by
    simp only [Array.size_extract, Nat.sub_zero, Nat.min_eq_left hfloor]
  by_cases hr : n % 8 = 0
  · have hbyte : (n + 7) / 8 = n / 8 := by omega
    apply Array.ext
    · simp [canonicalBytes, hr, packBits, hbyte, hs]
    · intro i hi _
      have hi' : i < n / 8 := by simpa only [packBits, Array.size_ofFn, hbyte] using hi
      have hsi : i < src.size := by omega
      simpa [packBits, canonicalBytes, hr, getElem!_pos, hsi] using
        packed_prefix_byte src n i hi'
  · have hbyte : (n + 7) / 8 = n / 8 + 1 := by omega
    apply Array.ext
    · simp [canonicalBytes, hr, packBits, hbyte, hs]
    · intro i hi _
      have hib : i < n / 8 + 1 := by simpa only [packBits, Array.size_ofFn, hbyte] using hi
      by_cases hi' : i < n / 8
      · have hsi : i < src.size := by omega
        simpa [packBits, canonicalBytes, hr, Array.getElem_push, hs, hi',
          getElem!_pos, hsi] using packed_prefix_byte src n i hi'
      · have heq : i = n / 8 := by omega
        subst i
        simpa [packBits, canonicalBytes, hr, Array.getElem_push, hs] using
          canonical_tail_byte src n

/-- Packing with a delimiter reproduces the native prefix and final-byte write. -/
theorem packBitsDelimited_unpackBits (src : Bytes) (n : Nat)
    (hsrc : src.size = (n + 7) / 8) :
    packBitsDelimited (unpackBits src n) = delimitedBytes src n := by
  have hfloor : n / 8 ≤ src.size := by omega
  have hs : (src.extract 0 (n / 8)).size = n / 8 := by
    simp only [Array.size_extract, Nat.sub_zero, Nat.min_eq_left hfloor]
  apply Array.ext
  · simp [packBitsDelimited, packBits, delimitedBytes, hs]
  · intro i hi _
    have hib : i < n / 8 + 1 := by simpa [packBitsDelimited, packBits] using hi
    by_cases hi' : i < n / 8
    · have hsi : i < src.size := by omega
      have hp := packByte_push_prefix (unpackBits src n) i (by simp; omega)
      have hc := hp.trans (packed_prefix_byte src n i hi')
      simpa [packBitsDelimited, packBits, delimitedBytes, Array.getElem_push,
        hs, hi', getElem!_pos, hsi] using hc
    · have heq : i = n / 8 := by omega
      subst i
      have tail := delimited_tail_byte src n
      by_cases hr : n % 8 = 0
      · simpa [packBitsDelimited, packBits, delimitedBytes, hr, Array.getElem_push, hs] using tail
      · simpa [packBitsDelimited, packBits, delimitedBytes, hr, Array.getElem_push, hs] using tail

/-- Fixed bit-vector serialization agrees with the native byte representation. -/
theorem serialize_bitVector (src : Bytes) (n : Nat) (hsrc : src.size = (n + 7) / 8) :
    serialize (.bitVector n) (.bits (unpackBits src n)) = .ok (canonicalBytes src n) := by
  simp only [serialize, unpackBits_size, beq_self_eq_true, ↓reduceIte,
    packBits_unpackBits_canonicalBytes src n hsrc]

/-- Canonical native bytes decode to their original logical bits. -/
theorem deserialize_bitVector (src : Bytes) (n : Nat) (hsrc : src.size = (n + 7) / 8) :
    deserialize (.bitVector n) (canonicalBytes src n) = .ok (.bits (unpackBits src n)) := by
  rw [← packBits_unpackBits_canonicalBytes src n hsrc]
  simpa only [unpackBits_size] using Packing.deserialize_bitVector (unpackBits src n)

/-- Bounded bit-list serialization uses the native delimited bytes. -/
theorem serialize_bitList (src : Bytes) (n cap : Nat) (hsrc : src.size = (n + 7) / 8)
    (hn : n ≤ cap) :
    serialize (.bitList cap) (.bits (unpackBits src n)) = .ok (delimitedBytes src n) := by
  simp only [serialize, unpackBits_size, hn, ↓reduceIte,
    packBitsDelimited_unpackBits src n hsrc]

/-- The native delimiter recovers precisely the data count and bits. -/
theorem deserialize_bitList (src : Bytes) (n cap : Nat) (hsrc : src.size = (n + 7) / 8)
    (hn : n ≤ cap) :
    deserialize (.bitList cap) (delimitedBytes src n) = .ok (.bits (unpackBits src n)) := by
  rw [← packBitsDelimited_unpackBits src n hsrc]
  have recovered := unpackDelimited_packBitsDelimited (some cap) (unpackBits src n)
    (by intro bound named; cases named; simpa using hn)
  simp only [deserialize, recovered] <;> rfl

/-- Progressive bit-list serialization covers both absent and arbitrary natural bounds. -/
theorem serialize_progressiveBitList (src : Bytes) (n : Nat) (limit : Option Nat)
    (hsrc : src.size = (n + 7) / 8) (within : withinBound limit n = true) :
    serialize (.progressiveBitList limit) (.bits (unpackBits src n)) =
      .ok (delimitedBytes src n) := by
  have checked : boundCheck limit n = .ok () := by
    cases limit <;> simp_all [withinBound, boundCheck]
  simp only [serialize, unpackBits_size, checked]
  exact congrArg (fun bytes => (Except.ok bytes : Except Err Bytes))
    (packBitsDelimited_unpackBits src n hsrc)

/-- Progressive decoding checks its optional bound and recovers the packed input. -/
theorem deserialize_progressiveBitList (src : Bytes) (n : Nat) (limit : Option Nat)
    (hsrc : src.size = (n + 7) / 8) (within : withinBound limit n = true) :
    deserialize (.progressiveBitList limit) (delimitedBytes src n) =
      .ok (.bits (unpackBits src n)) := by
  rw [← packBitsDelimited_unpackBits src n hsrc]
  have recovered := unpackDelimited_packBitsDelimited limit (unpackBits src n)
    (by intro bound named; subst limit; simpa [withinBound] using within)
  simp only [deserialize, recovered] <;> rfl

end SszNative.PackedBits

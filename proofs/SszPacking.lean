import Ssz.Proofs.Codec.Table

/-! Packing facts over the pinned definitions. These proofs follow upstream
`RoundTripScalar` without importing its unrelated `Admits` type-validity proofs,
whose `simp_all` calls exceed the recursion bound under the ARM backend's Lean version. -/

namespace SszNative.Packing

open Ssz

@[simp] theorem unpackBits_size (data : Bytes) (n : Nat) :
    (unpackBits data n).size = n := by simp [unpackBits]

/-- Each packed bit is the corresponding supplied bit, or zero padding. -/
theorem packByte_bit (bits : Array Bool) (byteIndex offset : Nat) (small : offset < 8) :
    ((packByte bits byteIndex >>> UInt8.ofNat offset) &&& 1 == 1) =
      bits[byteIndex * 8 + offset]?.getD false := by
  match offset, small with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp only [packByte]
    generalize bits[byteIndex * 8 + 0]?.getD false = b0
    generalize bits[byteIndex * 8 + 1]?.getD false = b1
    generalize bits[byteIndex * 8 + 2]?.getD false = b2
    generalize bits[byteIndex * 8 + 3]?.getD false = b3
    generalize bits[byteIndex * 8 + 4]?.getD false = b4
    generalize bits[byteIndex * 8 + 5]?.getD false = b5
    generalize bits[byteIndex * 8 + 6]?.getD false = b6
    generalize bits[byteIndex * 8 + 7]?.getD false = b7
    revert b0 b1 b2 b3 b4 b5 b6 b7
    decide

private theorem byte_testBit (byte : UInt8) (offset : Nat) (small : offset < 8) :
    ((byte >>> UInt8.ofNat offset) &&& 1 == 1) = byte.toNat.testBit offset := by
  have bound : offset < UInt8.size := by change offset < 256; omega
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, ← UInt8.toNat_inj, UInt8.toNat_and, UInt8.toNat_shiftRight,
    UInt8.toNat_ofNat_of_lt' bound, Nat.mod_eq_of_lt small, UInt8.toNat_one,
    Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq,
    decide_eq_true_eq]

/-- Shifting beyond the supplied bits leaves zero. -/
theorem packByte_high_clear (bits : Array Bool) (byteIndex offset : Nat)
    (small : offset < 8) (past : bits.size ≤ byteIndex * 8 + offset) :
    packByte bits byteIndex >>> UInt8.ofNat offset = 0 := by
  have offsetBound : offset < UInt8.size := by change offset < 256; omega
  apply UInt8.toNat_inj.mp
  simp only [UInt8.toNat_shiftRight, UInt8.toNat_ofNat_of_lt' offsetBound,
    Nat.mod_eq_of_lt small, UInt8.toNat_zero]
  apply Nat.eq_of_testBit_eq
  intro position
  rw [Nat.testBit_shiftRight, Nat.zero_testBit]
  by_cases within : offset + position < 8
  · rw [← byte_testBit _ _ within, packByte_bit _ _ _ within]
    rw [Array.getElem?_eq_none (by omega)]
    rfl
  · apply Nat.testBit_lt_two_pow
    have width := (packByte bits byteIndex).toNat_lt
    have power : 2 ^ 8 ≤ 2 ^ (offset + position) := Nat.pow_le_pow_right (by decide) (by omega)
    change (packByte bits byteIndex).toNat < 256 at width
    exact Nat.lt_of_lt_of_le width power

/-- Enough packed bytes retain every supplied bit. -/
theorem unpackBits_packBits (bits : Array Bool) (byteCount : Nat)
    (room : bits.size ≤ 8 * byteCount) :
    unpackBits (packBits bits byteCount) bits.size = bits := by
  apply Array.ext
  · simp
  · intro position _ inBits
    simp only [unpackBits, Array.getElem_map, Array.getElem_range]
    have inBytes : position / 8 < byteCount := by omega
    have byteIs : (packBits bits byteCount)[position / 8]! = packByte bits (position / 8) := by
      simp [packBits, getElem!_pos, inBytes]
    rw [byteIs, packByte_bit bits (position / 8) (position % 8) (by omega)]
    rw [show position / 8 * 8 + position % 8 = position by omega,
      Array.getElem?_eq_getElem inBits, Option.getD_some]

private theorem highestBit_eq (byte : UInt8) (offset : Nat) (small : offset < 8)
    (isSet : (byte >>> UInt8.ofNat offset) &&& 1 = 1)
    (above : ∀ j, offset < j → j < 8 → (byte >>> UInt8.ofNat j) &&& 1 ≠ 1) :
    highestBit byte = offset := by
  match offset, small with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    have h7 := above 7
    have h6 := above 6
    have h5 := above 5
    have h4 := above 4
    have h3 := above 3
    have h2 := above 2
    have h1 := above 1
    simp_all [highestBit]

private theorem unpackBits_packBits_push (bits : Array Bool) (byteCount : Nat)
    (room : bits.size + 1 ≤ 8 * byteCount) :
    unpackBits (packBits (bits.push true) byteCount) bits.size = bits := by
  apply Array.ext
  · simp
  · intro position _ inBits
    simp only [unpackBits, Array.getElem_map, Array.getElem_range]
    have inBytes : position / 8 < byteCount := by omega
    have byteIs : (packBits (bits.push true) byteCount)[position / 8]! =
        packByte (bits.push true) (position / 8) := by
      simp [packBits, getElem!_pos, inBytes]
    rw [byteIs, packByte_bit _ (position / 8) (position % 8) (by omega)]
    rw [show position / 8 * 8 + position % 8 = position by omega]
    rw [Array.getElem?_eq_getElem (by simp; omega), Option.getD_some,
      Array.getElem_push_lt inBits]

/-- The delimiter is found at exactly the original logical bit count. -/
theorem unpackDelimited_packBitsDelimited (limit : Option Nat) (data : Array Bool)
    (within : ∀ cap, limit = some cap → data.size ≤ cap) :
    unpackDelimited limit (packBitsDelimited data) = .ok data := by
  show unpackDelimited limit (packBits (data.push true) ((data.size + 8) / 8)) = .ok data
  have widthIs : (packBits (data.push true) ((data.size + 8) / 8)).size =
      (data.size + 8) / 8 := by simp [packBits]
  have finalIs : (packBits (data.push true) ((data.size + 8) / 8))[data.size / 8]! =
      packByte (data.push true) (data.size / 8) := by
    simp [packBits, getElem!_pos]
  have isSet : (packByte (data.push true) (data.size / 8) >>> UInt8.ofNat (data.size % 8))
      &&& 1 = 1 := by
    have found := packByte_bit (data.push true) (data.size / 8) (data.size % 8) (by omega)
    rw [show data.size / 8 * 8 + data.size % 8 = data.size by omega] at found
    simp only [Array.getElem?_eq_getElem (show data.size < (data.push true).size by simp),
      Option.getD_some, Array.getElem_push_eq] at found
    simpa using found
  have above : ∀ j, data.size % 8 < j → j < 8 →
      (packByte (data.push true) (data.size / 8) >>> UInt8.ofNat j) &&& 1 ≠ 1 := by
    intro j over small
    have clear := packByte_bit (data.push true) (data.size / 8) j small
    rw [Array.getElem?_eq_none (by simp; omega)] at clear
    simpa using clear
  have notZero : ¬ (packByte (data.push true) (data.size / 8) = 0) := by
    intro zero
    rw [zero] at isSet
    simp at isSet
  have counted : 8 * ((data.size + 8) / 8 - 1) +
      highestBit (packBits (data.push true) ((data.size + 8) / 8))[data.size / 8]! = data.size := by
    rw [finalIs, highestBit_eq _ (data.size % 8) (by omega) isSet above]
    omega
  have recovered : unpackBits (packBits (data.push true) ((data.size + 8) / 8)) data.size = data :=
    unpackBits_packBits_push data _ (by omega)
  simp only [unpackDelimited, widthIs, beq_iff_eq,
    show ¬ (data.size + 8) / 8 = 0 by omega, ↓reduceIte,
    show (data.size + 8) / 8 - 1 = data.size / 8 by omega, finalIs, notZero]
  rw [show (data.size + 8) / 8 - 1 = data.size / 8 by omega, finalIs] at counted
  cases limit with
  | none => simp only [counted, recovered, Pure.pure, Except.pure] <;> rfl
  | some cap =>
    have bounded : ¬ data.size > cap := by have := within cap rfl; omega
    simp only [counted, recovered, Pure.pure, Except.pure, bounded, ↓reduceIte] <;> rfl

/-- Packed fixed-length bits satisfy the decoder's exact-size and padding checks. -/
theorem deserialize_bitVector (data : Array Bool) :
    deserialize (.bitVector data.size) (packBits data ((data.size + 7) / 8)) =
      .ok (.bits data) := by
  have width : (packBits data ((data.size + 7) / 8)).size = (data.size + 7) / 8 := by
    simp [packBits]
  simp only [deserialize, width, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  have padded : ∀ h : data.size % 8 != 0 ∧ (data.size + 7) / 8 > 0,
      (packBits data ((data.size + 7) / 8))[(data.size + 7) / 8 - 1]! >>>
        UInt8.ofNat (data.size % 8) = 0 := by
    intro ⟨odd, room⟩
    have inBytes : (data.size + 7) / 8 - 1 < (data.size + 7) / 8 := by omega
    have byteIs : (packBits data ((data.size + 7) / 8))[(data.size + 7) / 8 - 1]! =
        packByte data ((data.size + 7) / 8 - 1) := by
      simp [packBits, getElem!_pos, inBytes]
    rw [byteIs]
    apply packByte_high_clear data _ _ (by omega)
    simp only [bne_iff_ne, ne_eq] at odd
    omega
  have unpacked := unpackBits_packBits data ((data.size + 7) / 8) (by omega)
  split
  · rename_i checked
    simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
    simp [padded checked, unpacked, Pure.pure, Except.pure] <;> rfl
  · simp [unpacked, Pure.pure, Except.pure] <;> rfl

end SszNative.Packing

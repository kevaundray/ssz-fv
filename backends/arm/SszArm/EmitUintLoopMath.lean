import SszArm.EmitUintOwned

namespace SszArm.Emit.Uint

open SszNative (NatOperand)

/-- The machine's wrapping bit counter retains precisely the three byte-index
bits needed for a limb shift, even after arbitrarily many 64-bit wraps. -/
theorem byte_shift_mask (index : Nat) :
    (BitVec.ofNat 64 (8 * index) &&& 56#64) = BitVec.ofNat 64 (8 * (index % 8)) := by
  have low : (BitVec.ofNat 64 (8 * index) &&& 63#64) = BitVec.ofNat 64 (8 * (index % 8)) := by
    apply BitVec.eq_of_toNat_eq
    change ((8 * index) % 2^64 &&& (2^6 - 1)) = (8 * (index % 8)) % 2^64
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  have mask : (BitVec.ofNat 64 (8 * index) &&& 56#64) =
      ((BitVec.ofNat 64 (8 * index) &&& 63#64) &&& 56#64) := by
    rw [BitVec.and_assoc]
    rfl
  rw [mask, low]
  have residues : index % 8 = 0 ∨ index % 8 = 1 ∨ index % 8 = 2 ∨ index % 8 = 3 ∨
      index % 8 = 4 ∨ index % 8 = 5 ∨ index % 8 = 6 ∨ index % 8 = 7 := by omega
  rcases residues with equal | equal | equal | equal | equal | equal | equal | equal <;>
    rw [equal] <;> decide

theorem byte_shift_count (index : Nat) :
    (BitVec.ofNat 64 (8 * index) &&& 56#64).toNat % 64 = 8 * (index % 8) := by
  rw [byte_shift_mask, BitVec.toNat_ofNat]
  omega

theorem small_word_at (word : BitVec 64) (index : Nat) :
    ([word][index / 8]?.getD 0) = if index < 8 then word else 0#64 := by
  by_cases small : index < 8
  · have quotient : index / 8 = 0 := by omega
    simp [small, quotient]
  · have positive : 0 < index / 8 := by omega
    cases quotient : index / 8 with
    | zero => omega
    | succ rest => simp [small, quotient]

/-- The exact zero-extended logical limb selected by the native loop. -/
def emittedWord (number : NatOperand) (index : Nat) : BitVec 64 :=
  number.words[index / 8]?.getD 0

theorem emittedWord_small (word : BitVec 64) (index : Nat) :
    emittedWord (.small word) index = if index < 8 then word else 0#64 := by
  exact small_word_at word index

theorem emitted_byte (number : NatOperand) (index : Nat) :
    (((emittedWord number index) >>> (8 * (index % 8))).setWidth 8).toNat =
      (SszNative.Limbs.byteAt number.words index).toNat := by
  simp only [emittedWord, SszNative.Limbs.byteAt, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, UInt8.toNat_ofNat]
  rfl

theorem emitted_array_byte (number : NatOperand) (size index : Nat) (inside : index < size) :
    ((SszNative.Limbs.bytes number.words size)[index]?.getD 0).toNat =
      (SszNative.Limbs.byteAt number.words index).toNat := by
  simp [SszNative.Limbs.bytes, Array.getElem?_eq_getElem, inside]

end SszArm.Emit.Uint

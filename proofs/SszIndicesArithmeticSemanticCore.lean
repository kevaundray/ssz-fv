import SszIndicesCore

set_option autoImplicit false

namespace SszNative.Indices

/-- A finite raw limb list is observed without a canonicality assumption. -/
theorem limbs_word_bit (words : List (BitVec 64)) (position offset : Nat)
    (inside : offset < 64) :
    (words[position]?.getD 0).toNat.testBit offset =
      (Limbs.value words).testBit (64 * position + offset) := by
  induction words generalizing position with
  | nil => simp [Limbs.value]
  | cons first rest ih =>
      cases position with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.getD_some, Nat.mul_zero,
            Nat.zero_add, Limbs.value]
          rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ first.isLt]
          simp [inside]
      | succ position =>
          simp only [List.getElem?_cons_succ, Limbs.value]
          rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ first.isLt]
          have beyond : ¬64 * (position + 1) + offset < 64 := by omega
          simp only [beyond, ↓reduceIte]
          rw [show 64 * (position + 1) + offset - 64 = 64 * position + offset by omega]
          exact ih position

/-- Every raw representation has a width bounded by its physical storage. -/
theorem bitLength_le_storage (index : NatOperand) :
    bitLength index ≤ 64 * index.words.length := by
  rw [bitLength_value]
  unfold Serialize.bitLength
  split
  · omega
  · rename_i nonzero
    have bounded := (Nat.log2_lt nonzero).mpr (Limbs.value_lt index.words)
    change index.value.log2 < 64 * index.words.length at bounded
    omega

theorem bitLength_u128 (index : NatOperand) (physical : index.words.length < 2 ^ 64) :
    bitLength index < 2 ^ 128 := by
  have bound := bitLength_le_storage index
  omega

/-- Mapped input storage supplies the only host-size bound used by bit reads. -/
theorem physical_of_at (index : NatOperand) (observe : Nat → Nat → Option Nat)
    (stored : index.At observe) : index.words.length < 2 ^ 64 := by
  cases index with
  | small value => simp [NatOperand.words]
  | large pointer words =>
      obtain ⟨positive, aligned, bounded, contents⟩ := stored
      change words.length < 2 ^ 64
      omega

/-- The u64 mask comparison is precisely the selected natural bit. -/
theorem masked_bit (value : BitVec 64) (position : Nat) :
    (((value >>> position) &&& 1) != 0) = value.toNat.testBit position := by
  apply Bool.eq_iff_iff.mpr
  simp only [Nat.testBit, bne_iff_ne, BitVec.toNat_ne, BitVec.toNat_and,
    BitVec.toNat_ushiftRight]
  change (value.toNat >>> position &&& 1 ≠ 0) ↔ (1 &&& value.toNat >>> position ≠ 0)
  rw [Nat.and_comm (value.toNat >>> position) 1]

/-- The public native bit operation refines the pinned gindex observation.
The domain constrains physical storage, not the represented natural's magnitude. -/
theorem bit_refines (index : NatOperand) (position : Nat)
    (physical : index.words.length < 2 ^ 64) :
    bit index position = Ssz.gindexBit index.value position := by
  unfold bit Ssz.gindexBit
  by_cases offset : position / 64 < 2 ^ 64
  · simp only [offset, ↓reduceIte]
    rw [masked_bit, word_eq,
      limbs_word_bit index.words (position / 64) (position % 64) (Nat.mod_lt _ (by decide))]
    congr 1
    omega
  · simp only [offset, ↓reduceIte]
    have width : 64 * index.words.length ≤ position := by omega
    have magnitude := Limbs.value_lt index.words
    have power : 2 ^ (64 * index.words.length) ≤ 2 ^ position :=
      Nat.pow_le_pow_right (by decide) width
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le magnitude power)).symm

/-- Empty borrowed storage remains a valid raw zero operand. -/
theorem empty_large_bitLength (pointer : BitVec 64) :
    bitLength (.large pointer []) = 0 := by
  rw [bitLength_value]
  rfl

theorem padded_bitLength (index : NatOperand) (pointer : BitVec 64) (padding : Nat) :
    bitLength (.large pointer (index.words ++ List.replicate padding 0)) = bitLength index := by
  rw [bitLength_value, bitLength_value]
  simp only [NatOperand.value, NatOperand.words, Limbs.value_append_zero]

end SszNative.Indices

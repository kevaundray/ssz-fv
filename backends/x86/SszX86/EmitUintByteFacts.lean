import SszX86.EmitUintInstructions

namespace SszX86.Emit.Uint
open SszNative
open Instructions (low8 low32)

/-- Only the low byte controls SHR; MOVL's zero-extension and the partial CL
writes do not truncate the logical byte index. -/
def pairCount (index : Nat) : BitVec 64 :=
  let counter := low32 (BitVec.ofNat 64 (8 * index))
  counter.replaceLow (low8 counter &&& 48#8)

def oddCount (index : Nat) : BitVec 64 :=
  (pairCount index).replaceLow (low8 (pairCount index) ||| 8#8)

theorem low8_replace (v : BitVec 64) (byte : BitVec 8) :
    low8 (v.replaceLow byte) = byte := by
  unfold low8
  rw [BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)]
  simp only [BitVec.replaceLow, BitVec.setWidth_eq]
  exact BitVec.extractLsb'_append_eq_right (a := v.drop 8) (b := byte)

theorem counter_low (index : Nat) :
    low8 (low32 (BitVec.ofNat 64 (8 * index))) =
      BitVec.ofNat 8 (8 * (index % 32)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [low8, low32, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem even_residues (index : Nat) (even : index % 2 = 0) :
    index % 32 = 0 ∨ index % 32 = 2 ∨ index % 32 = 4 ∨ index % 32 = 6 ∨
    index % 32 = 8 ∨ index % 32 = 10 ∨ index % 32 = 12 ∨ index % 32 = 14 ∨
    index % 32 = 16 ∨ index % 32 = 18 ∨ index % 32 = 20 ∨ index % 32 = 22 ∨
    index % 32 = 24 ∨ index % 32 = 26 ∨ index % 32 = 28 ∨ index % 32 = 30 := by
  omega

/-- The sixteen alternatives are only the finite CL residue, not a width bound.
This remains valid when the counter wraps repeatedly at 2^64. -/
theorem pair_shift (index : Nat) (even : index % 2 = 0) :
    (low8 (pairCount index)).toNat &&& 63 = 8 * (index % 8) := by
  rw [pairCount, low8_replace, counter_low]
  have cases := even_residues index even
  rcases cases with h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h
  all_goals
    have remainder : index % 8 = (index % 32) % 8 := by omega
    rw [remainder, h]
    decide

theorem odd_shift (index : Nat) (even : index % 2 = 0) :
    (low8 (oddCount index)).toNat &&& 63 = 8 * ((index + 1) % 8) := by
  rw [oddCount, low8_replace, pairCount, low8_replace, counter_low]
  have cases := even_residues index even
  rcases cases with h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h
  all_goals
    have remainder : (index + 1) % 8 = ((index % 32) + 1) % 8 := by omega
    rw [remainder, h]
    decide

theorem pair_same_limb (index : Nat) (even : index % 2 = 0) :
    (index + 1) / 8 = index / 8 := by omega

/-- The native even-length AND is floor-to-even at every representable width. -/
theorem even_length (byteCount : Nat) (bound : byteCount < 2 ^ 64) :
    BitVec.ofNat 64 byteCount &&& 0xfffffffffffffffe#64 =
      BitVec.ofNat 64 (2 * (byteCount / 2)) := by
  rw [show 0xfffffffffffffffe#64 = BitVec.allOnes 64 <<< (1 : Nat) by decide,
    ← BitVec.shiftLeft_ushiftRight]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt bound, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.pow_one]
  omega

/-- Shift extraction agrees with the shared arbitrary-limb source model. -/
theorem shifted_limb_byte (words : List (BitVec 64)) (index : Nat) :
    UInt8.ofBitVec (((words[index / 8]?.getD 0) >>> (8 * (index % 8))).setWidth 8) =
      Limbs.byteAt words index := by
  apply UInt8.toNat_inj.mp
  simp only [UInt8.toNat_ofBitVec, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Limbs.byteAt, UInt8.toNat_ofNat']

theorem small_limb (limb : BitVec 64) (index : Nat) :
    ((NatOperand.small limb).words[index / 8]?.getD 0) =
      if index < 8 then limb else 0 := by
  by_cases within : index < 8
  · simp [NatOperand.words, Nat.div_eq_of_lt within, within]
  · simp [NatOperand.words, within]

/-- The scalar remainder's SHLL truncates only a shift counter; the hardware
mask recovers the right byte position even beyond 2^32 bytes. -/
theorem tail_shift (index : Nat) :
    (low8 (low32 (((BitVec.ofNat 64 index).setWidth 32 <<< (3 : Nat)).setWidth 64))).toNat
      &&& 63 = 8 * (index % 8) := by
  simp only [low8, low32, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

end SszX86.Emit.Uint

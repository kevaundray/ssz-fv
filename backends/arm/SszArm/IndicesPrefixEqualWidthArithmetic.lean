import SszArm.IndicesPrefixEqualWidthRows

namespace SszArm.Indices.PrefixEqual.Width

open Udivti3 (join radix)
open SszNative (NatOperand)
open SszNative.Limbs

/-- The two original shift words reconstruct every supplied u128 value. -/
theorem join_u128 (value : BitVec 128) :
    join (value.setWidth 64) ((value >>> 64).setWidth 64) = value.toNat := by
  have bound := value.isLt
  simp only [join, radix, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  omega

/-- The compiler's LSL/LSR pair retains the overflow of a 64-bit limb count. -/
theorem shift_pair (value : BitVec 64) :
    join (value <<< 6) (value >>> 58) = 64 * value.toNat := by
  have bound := value.isLt
  simp only [join, radix, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

/-- The large-width prefix is 64*(significantCount-1), not a wrapped usize
product. The ADC after SUBS propagates the real borrow into the upper word. -/
theorem base_width (value : BitVec 64) (positive : 0 < value.toNat) :
    join (AddWithCarry (value <<< 6) (~~~64#64) 1#1).1
      (AddWithCarry (value >>> 58) (-1#64)
        (AddWithCarry (value <<< 6) (~~~64#64) 1#1).2.c).1 =
      64 * (value.toNat - 1) := by
  have balance := ShiftXor.wide_sub_balance (value <<< 6) (value >>> 58) 64#64 0#64
  have carry := (ShiftXor.wide_sub_carry (value <<< 6) (value >>> 58) 64#64 0#64).mpr
    (by rw [shift_pair]; simp [join, radix]; omega)
  simp only [ShiftXor.highSub, ShiftXor.lowSub,
    show (~~~(0#64)) = -1#64 from rfl] at balance carry
  rw [carry, shift_pair] at balance
  simp only [join, radix, BitVec.toNat_ofNat] at balance
  change _ = 64 * (value.toNat - 1)
  simp only [join, radix]
  omega

/-- Converting the CLZ counter back through the actual W-register subtraction
cannot lose a bit: the operand's width is in the closed interval [0,64]. -/
theorem uncount_clz (value : BitVec 64) :
    ((64#32 - (BitVec.ofNat 64 (64 - SszNative.Serialize.bitLength value.toNat)).setWidth 32)
      .setWidth 64) = BitVec.ofNat 64 (SszNative.Serialize.bitLength value.toNat) := by
  have bound := (Measure.Uint.bitLength_shift_facts value).1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- Both paths of the compiler's carry branch implement the same u128 sum.
The bound follows from physical storage; it is not a logical Nat restriction. -/
theorem add_width (low high word : BitVec 64)
    (bounded : join low high + word.toNat < 2^128) :
    join (AddWithCarry low word 0#1).1
      (if (AddWithCarry low word 0#1).2.c = 1#1 then high + 1#64 else high) =
        join low high + word.toNat := by
  have balance := ShiftXor.adc_balance low word 0#1
  have carryBound := (AddWithCarry low word 0#1).2.c.isLt
  have resultBound := (AddWithCarry low word 0#1).1.isLt
  have highBound := high.isLt
  have carryEq : (AddWithCarry low word 0#1).2.c = 1#1 ↔
      (AddWithCarry low word 0#1).2.c.toNat = 1 :=
    ⟨fun h => congrArg BitVec.toNat h, fun h => BitVec.eq_of_toNat_eq h⟩
  by_cases carried : (AddWithCarry low word 0#1).2.c = 1#1
  · have one := carryEq.mp carried
    simp only [carried, ↓reduceIte, join, radix, BitVec.toNat_add,
      show (1#64).toNat = 1 from rfl]
    simp only [join, radix] at bounded
    simp only [radix, show (0#1).toNat = 0 from rfl, one] at balance
    omega
  · have zero : (AddWithCarry low word 0#1).2.c.toNat = 0 := by
      have : (AddWithCarry low word 0#1).2.c.toNat ≠ 1 := fun h => carried (carryEq.mpr h)
      omega
    simp only [carried, ↓reduceIte, join, radix]
    simp only [radix, show (0#1).toNat = 0 from rfl, zero] at balance
    omega

/-- Exact raw representation bridge after the descending scan. Redundant high
zeros and empty Large are deliberately retained in the original operand. -/
theorem large_width (pointer : BitVec 64) (words : List (BitVec 64)) :
    SszNative.Indices.bitLength (.large pointer words) =
      if sigWords words = 0 then 0 else
        64 * (sigWords words - 1) +
          SszNative.Serialize.bitLength (words[sigWords words - 1]?.getD 0).toNat := by
  by_cases empty : sigWords words = 0
  · simp [SszNative.Indices.bitLength, NatOperand.wordCount, NatOperand.words, empty]
  · have nonzero := SszNative.Serialize.significant_top_nonzero words words.length
      (show 0 < sigWords words by omega)
    have nonzeroNat : (words[sigWords words - 1]?.getD 0).toNat ≠ 0 := by
      intro zero
      apply nonzero
      exact BitVec.eq_of_toNat_eq zero
    simp [SszNative.Indices.bitLength, NatOperand.wordCount, NatOperand.words,
      SszNative.Indices.word, SszNative.Serialize.bitLength, empty, nonzeroNat,
      Nat.add_assoc]

theorem small_width (value : BitVec 64) :
    SszNative.Indices.bitLength (.small value) = SszNative.Serialize.bitLength value.toNat := by
  rw [SszNative.Indices.bitLength_value]
  simp [NatOperand.value, NatOperand.words, SszNative.Limbs.value]

end SszArm.Indices.PrefixEqual.Width

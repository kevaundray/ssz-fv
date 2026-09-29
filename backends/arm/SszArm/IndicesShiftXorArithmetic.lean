import SszArm.Udivti3Arithmetic

set_option autoImplicit false

namespace SszArm.Indices.ShiftXor

open SszArm.Udivti3 (join radix)

/-- Integer balance for the actual LNSym AddWithCarry operation. -/
theorem adc_balance (left right : BitVec 64) (carry : BitVec 1) :
    (AddWithCarry left right carry).1.toNat +
      radix * (AddWithCarry left right carry).2.c.toNat =
        left.toNat + right.toNat + carry.toNat := by
  have carried := Udivti3.adc_carry_nat left right carry
  have leftBound := left.isLt
  have rightBound := right.isLt
  have carryBound := carry.isLt
  rw [Udivti3.adc_value, BitVec.toNat_add, BitVec.toNat_add,
    BitVec.toNat_setWidth]
  dsimp only [radix] at carried ⊢
  omega

/-- Low SUBS and high SBCS, preserving the real carry chain. -/
def lowSub (left right : BitVec 64) : BitVec 64 × PState :=
  AddWithCarry left (~~~right) 1#1

def highSub (leftLow leftHigh rightLow rightHigh : BitVec 64) : BitVec 64 × PState :=
  AddWithCarry leftHigh (~~~rightHigh) (lowSub leftLow rightLow).2.c

/-- The radix-squared term is the no-borrow flag, not a logical size cap. -/
theorem wide_sub_balance (leftLow leftHigh rightLow rightHigh : BitVec 64) :
    join (lowSub leftLow rightLow).1
        (highSub leftLow leftHigh rightLow rightHigh).1 +
      join rightLow rightHigh +
      (radix * radix) * (highSub leftLow leftHigh rightLow rightHigh).2.c.toNat =
        join leftLow leftHigh + radix * radix := by
  have low := adc_balance leftLow (~~~rightLow) 1#1
  have high := adc_balance leftHigh (~~~rightHigh) (lowSub leftLow rightLow).2.c
  have rightLowBound := rightLow.isLt
  have rightHighBound := rightHigh.isLt
  simp only [BitVec.toNat_not, show (1#1).toNat = 1 from rfl] at low high
  change (lowSub leftLow rightLow).1.toNat +
    radix * (lowSub leftLow rightLow).2.c.toNat = _ at low
  change (highSub leftLow leftHigh rightLow rightHigh).1.toNat +
    radix * (highSub leftLow leftHigh rightLow rightHigh).2.c.toNat = _ at high
  dsimp only [join, radix] at low high ⊢
  omega

/-- The final SBCS flag is exactly the full unsigned u128 comparison. -/
theorem wide_sub_carry (leftLow leftHigh rightLow rightHigh : BitVec 64) :
    (highSub leftLow leftHigh rightLow rightHigh).2.c = 1#1 ↔
      join rightLow rightHigh ≤ join leftLow leftHigh := by
  have balance := wide_sub_balance leftLow leftHigh rightLow rightHigh
  have resultBound := Udivti3.join_lt (lowSub leftLow rightLow).1
    (highSub leftLow leftHigh rightLow rightHigh).1
  have leftBound := Udivti3.join_lt leftLow leftHigh
  have rightBound := Udivti3.join_lt rightLow rightHigh
  have carryBound := (highSub leftLow leftHigh rightLow rightHigh).2.c.isLt
  have carryEq : (highSub leftLow leftHigh rightLow rightHigh).2.c = 1#1 ↔
      (highSub leftLow leftHigh rightLow rightHigh).2.c.toNat = 1 :=
    ⟨fun equality => congrArg BitVec.toNat equality,
      fun equality => BitVec.eq_of_toNat_eq equality⟩
  rw [carryEq]
  dsimp only [radix] at balance
  omega

/-- Exact value selected by the two CSELs after SUBS/SBCS in shift_xor and
prefix_equal. Underflow returns zero; successful subtraction keeps both words. -/
theorem saturating_subtract (leftLow leftHigh rightLow rightHigh : BitVec 64) :
    (if (highSub leftLow leftHigh rightLow rightHigh).2.c = 1#1 then
      join (lowSub leftLow rightLow).1 (highSub leftLow leftHigh rightLow rightHigh).1
    else 0) = join leftLow leftHigh - join rightLow rightHigh := by
  have balance := wide_sub_balance leftLow leftHigh rightLow rightHigh
  have order := wide_sub_carry leftLow leftHigh rightLow rightHigh
  by_cases retained : (highSub leftLow leftHigh rightLow rightHigh).2.c = 1#1
  · simp only [retained, ↓reduceIte, show (1#1).toNat = 1 from rfl] at balance ⊢
    dsimp only [radix] at balance
    omega
  · simp only [retained, ↓reduceIte]
    have less : join leftLow leftHigh < join rightLow rightHigh := by
      have : ¬ join rightLow rightHigh ≤ join leftLow leftHigh := fun h => retained (order.mpr h)
      omega
    omega

end SszArm.Indices.ShiftXor

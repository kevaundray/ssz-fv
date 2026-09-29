import SszArm.NatMulWordSmallFrame

namespace SszArm.NatMulWord

open SszNative (NatOperand)
open SszNative.NatArithmetic

/-- The split lowering reconstructs the checked full-width product exactly. -/
theorem small_word_product (operand : NatOperand) (factor : BitVec 64) :
    SszNative.NatMul.wordProduct operand factor =
      NatMulProduct.high (SszNative.NatMul.lowWord operand) factor ++
        (SszNative.NatMul.lowWord operand * factor) := by
  apply BitVec.eq_of_toNat_eq
  rw [SszNative.NatMul.wordProduct,
    SszNative.LimbMul.wideProduct_toNat _ _ _ _ (by decide), NatToU128.append_toNat]
  arm_word_nf
  simpa only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_add, Nat.add_zero, Nat.add_comm] using
    (NatMulProduct.product_value (SszNative.NatMul.lowWord operand) factor).symm

theorem small_narrow_model (operand : NatOperand) (factor : BitVec 64)
    (address capacity used : Nat) (nonzero : factor ≠ 0#64) (notone : factor ≠ 1#64)
    (small : operand.wordCount ≤ 1)
    (narrow : NatMulProduct.high (SszNative.NatMul.lowWord operand) factor = 0#64) :
    SszNative.NatMul.runWord operand factor address capacity used =
      unchanged used (.ok (.small (SszNative.NatMul.lowWord operand * factor))) := by
  rw [SszNative.NatMul.runWord_small operand factor address capacity used nonzero notone small,
    fromWide, small_word_product, narrow]
  have bound : (0#64 ++ (SszNative.NatMul.lowWord operand * factor)).toNat < 2^64 := by
    rw [NatToU128.append_toNat]
    simpa using (SszNative.NatMul.lowWord operand * factor).isLt
  have low : (0#64 ++ (SszNative.NatMul.lowWord operand * factor)).setWidth 64 =
      SszNative.NatMul.lowWord operand * factor :=
    BitVec.eq_of_toNat_eq (NatToU128.append_low _ _)
  simp only [bound, ↓reduceIte, low]

end SszArm.NatMulWord

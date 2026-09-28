import SszArm.NatMulProductCarry

namespace SszArm.NatMulWord

@[simp] theorem product_carry_zero (value : BitVec 64) :
    NatMulProduct.carryWord value 0#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [NatMulProduct.carryWord_toNat]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero]
  exact Nat.div_eq_of_lt value.isLt

theorem product_high_comm (left right : BitVec 64) :
    NatMulProduct.high left right = NatMulProduct.high right left := by
  rw [NatMulProduct.high_eq, NatMulProduct.high_eq, Nat.mul_comm]

/-- The word loop's actual multiply, ADDS, and conditional high increment. -/
theorem word_step (word factor carry : BitVec 64) :
    SszNative.LimbMul.step factor word 0#64 carry.toNat =
      (word * factor + carry,
        (NatMulProduct.high word factor +
          (if (AddWithCarry (word * factor) carry 0#1).2.c = 1#1 then 1#64 else 0#64)).toNat) := by
  rw [NatMulProduct.step_eq_carry_first]
  simp only [BitVec.add_zero, product_carry_zero]
  rw [BitVec.mul_comm factor word, product_high_comm factor word,
    NatMulProduct.carryWord_eq_cset]

end SszArm.NatMulWord

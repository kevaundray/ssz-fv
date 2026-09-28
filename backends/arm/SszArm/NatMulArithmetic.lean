import SszArm.DelimitedExecCommon

namespace SszArm.NatMulArithmetic

@[simp] theorem lsr32_mask (v : BitVec 64) :
    v.rotateRight 32 &&& 4294967295#64 = v >>> 32 := by
  rw [show 4294967295#64 = (BitVec.allOnes 32).setWidth 64 by decide]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_rotateRight, BitVec.getLsbD_ushiftRight]
  by_cases h : i < 32
  · simp [h, hi, show 32 + i < 64 by omega]
  · have hx : v.getLsbD (32 + i) = false := BitVec.getLsbD_of_ge v (32 + i) (by omega)
    simp [h, hi, hx]

@[simp] theorem carry_result (a b : BitVec 64) (carry : BitVec 1) :
    (AddWithCarry a b carry).1 = a + b + carry.setWidth 64 := by
  by_cases zero : carry = 0#1
  · simp [zero, fst_AddWithCarry_eq_add]
  · have one : carry = 1#1 := by bv_omega
    rw [one, fst_AddWithCarry_eq_sub_neg]
    bv_omega

end SszArm.NatMulArithmetic

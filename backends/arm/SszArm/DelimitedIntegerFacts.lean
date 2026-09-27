import SszArm.DelimitedExecCommon

namespace SszArm.Delimited

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem and_ones64 (v : BitVec 64) : v &&& 18446744073709551615#64 = v :=
  BitVec.and_allOnes

theorem lsl24_full_mask (v : BitVec 32) :
    (v.rotateRight 8).setWidth 64 &&& 4278190080#64 &&& 4294967295#64 =
      (v <<< 24).setWidth 64 := by
  rw [BitVec.and_assoc,
    show 4278190080#64 &&& 4294967295#64 = 4278190080#64 by decide,
    lsl24_mask]

/-- A 32-bit SXTB sign-extends its low byte to 32 bits, then clears the upper
half of the destination X register. It is not a 64-bit sign extension. -/
theorem sxt_byte_mask (v : BitVec 32) :
    ((v.extractLsb' 7 1).replicate 32).setWidth 64 &&& 4294967040#64 |||
      ((v.rotateRight 0).setWidth 64 &&& 255#64 &&& 255#64) =
        ((v.setWidth 8).signExtend 32).setWidth 64 := by
  rw [show 4294967040#64 = (BitVec.allOnes 24).setWidth 64 <<< 8 by decide,
    show 255#64 = (BitVec.allOnes 8).setWidth 64 by decide]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_replicate, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_allOnes, BitVec.getLsbD_rotateRight, BitVec.getLsbD_signExtend,
    BitVec.msb_eq_getLsbD_last, Nat.mul_one, Nat.one_mul, Nat.mod_one,
    Nat.add_zero, Nat.zero_add]
  by_cases low : i < 8
  · simp [low, hi, show i < 32 by omega, show i < 64 by omega]
  · by_cases middle : i < 32
    · simp [low, middle, hi, show i - 8 < 24 by omega, show i - 8 < 64 by omega]
    · simp [low, middle, hi, show ¬ i - 8 < 24 by omega]

end SszArm.Delimited

import SszArm.UintExec

namespace SszArm.UintCodec

set_option maxHeartbeats 2000000

/-- A concrete all-ones mask retained by UBFM simplification. -/
theorem uint_and_ones (v : BitVec 64) : v &&& 18446744073709551615#64 = v := by
  exact BitVec.and_allOnes

/-- The actual UBFM mask for an unsigned three-bit right shift. -/
theorem uint_lsr3_mask (v : BitVec 64) :
    v.rotateRight 3 &&& 2305843009213693951#64 = v >>> 3 := by
  rw [show 2305843009213693951#64 = (BitVec.allOnes 61).setWidth 64 by decide]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_rotateRight, BitVec.getLsbD_ushiftRight]
  by_cases h : i < 61
  · simp [h, hi, show 3 + i < 64 by omega]
  · have hx : v.getLsbD (3 + i) = false := BitVec.getLsbD_of_ge v (3 + i) (by omega)
    simp [h, hi, hx]

/-- The actual UBFM mask for scaling a byte offset by eight. -/
theorem uint_lsl3_mask (v : BitVec 64) :
    v.rotateRight 61 &&& 18446744073709551608#64 = v <<< 3 := by
  rw [show 18446744073709551608#64 = BitVec.allOnes 64 <<< 3 by decide]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_rotateRight,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes]
  by_cases h : i < 3
  · simp [h, hi]
  · simp [h, hi, show i - 3 < 64 by omega]

end SszArm.UintCodec

import SszArm.MeasureUintCountOps

namespace SszArm.Measure.Uint

theorem count_lsr1_mask (value : BitVec 64) :
    value.rotateRight 1 &&& 9223372036854775807#64 = value >>> 1 := by
  rw [show 9223372036854775807#64 = (BitVec.allOnes 63).setWidth 64 by decide]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro index bound
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_rotateRight, BitVec.getLsbD_ushiftRight]
  by_cases low : index < 63
  · simp [low, bound, show 1 + index < 64 by omega]
  · have outside := BitVec.getLsbD_of_ge value (1 + index) (by omega)
    simp [low, bound, outside]

theorem count_lsr58_mask (value : BitVec 64) :
    value.rotateRight 58 &&& 63#64 = value >>> 58 := by
  rw [show 63#64 = (BitVec.allOnes 6).setWidth 64 by decide]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro index bound
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_rotateRight, BitVec.getLsbD_ushiftRight]
  by_cases low : index < 6
  · simp [low, bound, show 58 + index < 64 by omega]
  · have outside := BitVec.getLsbD_of_ge value (58 + index) (by omega)
    simp [low, bound, outside]

theorem count_lsl6_mask (value : BitVec 64) :
    value.rotateRight 58 &&& 18446744073709551552#64 = value <<< 6 := by
  rw [show 18446744073709551552#64 = BitVec.allOnes 64 <<< 6 by decide]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro index bound
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_rotateRight,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes]
  by_cases low : index < 6
  · simp [low, bound]
  · simp [low, bound, show index - 6 < 64 by omega]

end SszArm.Measure.Uint

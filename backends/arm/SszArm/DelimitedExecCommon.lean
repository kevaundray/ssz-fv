import SszArm.DelimitedOps

namespace SszArm.Delimited

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem lsr61_mask (v : BitVec 64) :
    v.rotateRight 61 &&& 7#64 = v >>> 61 := by
  rw [show 7#64 = (BitVec.allOnes 3).setWidth 64 by decide]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_rotateRight, BitVec.getLsbD_ushiftRight]
  by_cases h : i < 3
  · simp [h, hi, show 61 + i < 64 by omega]
  · have hx : v.getLsbD (61 + i) = false := BitVec.getLsbD_of_ge v (61 + i) (by omega)
    simp [h, hi, hx]

theorem lsr1_mask (v : BitVec 32) :
    (v.rotateRight 1).setWidth 64 &&& 4294967295#64 &&& 2147483647#64 =
      (v >>> 1).setWidth 64 := by
  rw [show 4294967295#64 = (BitVec.allOnes 32).setWidth 64 by decide,
    show 2147483647#64 = (BitVec.allOnes 31).setWidth 64 by decide]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_rotateRight, BitVec.getLsbD_ushiftRight]
  by_cases h : i < 31
  · simp [h, hi, show i < 32 by omega, show 1 + i < 32 by omega]
  · have hx : v.getLsbD (1 + i) = false := BitVec.getLsbD_of_ge v (1 + i) (by omega)
    simp [h, hi, hx]

theorem lsl24_mask (v : BitVec 32) :
    (v.rotateRight 8).setWidth 64 &&& 4278190080#64 = (v <<< 24).setWidth 64 := by
  rw [show 4278190080#64 = ((BitVec.allOnes 32) <<< 24).setWidth 64 by decide]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_rotateRight,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes]
  by_cases h : i < 24
  · simp [h, hi, show i < 32 by omega]
  · by_cases h32 : i < 32
    · simp [h, hi, h32, show i - 24 < 32 by omega]
    · simp [h32]

end SszArm.Delimited

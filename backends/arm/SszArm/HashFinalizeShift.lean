import SszArm.HashFinalizeEndian

namespace SszArm.Hash.Finalize

theorem lsr8_ubfm (x : BitVec 32) :
    BitVec.ror x 8 &&& 16777215#32 = x >>> (8 : Nat) := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit bound
  match bit, bound with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ | 25, _ | 26, _ | 27, _ | 28, _ | 29, _ | 30, _ | 31, _ =>
    simp [BitVec.ror, BitVec.getLsbD_rotateRight]
  | bit + 32, bound => omega

theorem lsr16_ubfm (x : BitVec 32) :
    BitVec.ror x 16 &&& 65535#32 = x >>> (16 : Nat) := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit bound
  match bit, bound with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ | 25, _ | 26, _ | 27, _ | 28, _ | 29, _ | 30, _ | 31, _ =>
    simp [BitVec.ror, BitVec.getLsbD_rotateRight]
  | bit + 32, bound => omega

theorem lsr24_ubfm (x : BitVec 32) :
    BitVec.ror x 24 &&& 255#32 = x >>> (24 : Nat) := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit bound
  match bit, bound with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ | 25, _ | 26, _ | 27, _ | 28, _ | 29, _ | 30, _ | 31, _ =>
    simp [BitVec.ror, BitVec.getLsbD_rotateRight]
  | bit + 32, bound => omega

theorem lsl3_ubfm (x : BitVec 64) :
    BitVec.ror x 61 &&& 18446744073709551608#64 = x <<< (3 : Nat) := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit bound
  match bit, bound with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ | 25, _ | 26, _ | 27, _ | 28, _ | 29, _ | 30, _ | 31, _ | 32, _ | 33, _ | 34, _ | 35, _ | 36, _ | 37, _ | 38, _ | 39, _ | 40, _ | 41, _ | 42, _ | 43, _ | 44, _ | 45, _ | 46, _ | 47, _ | 48, _ | 49, _ | 50, _ | 51, _ | 52, _ | 53, _ | 54, _ | 55, _ | 56, _ | 57, _ | 58, _ | 59, _ | 60, _ | 61, _ | 62, _ | 63, _ =>
    simp [BitVec.ror, BitVec.getLsbD_rotateRight]
  | bit + 64, bound => omega

end SszArm.Hash.Finalize

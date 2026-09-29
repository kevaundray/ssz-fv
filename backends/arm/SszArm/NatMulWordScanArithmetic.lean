import SszArm.NatMulWordScanStages
import SszArm.WordNormalize

namespace SszArm.NatMulWord

theorem trim_remaining_sum (length remaining : Nat) :
    BitVec.ofNat 64 length + (BitVec.ofNat 64 remaining - BitVec.ofNat 64 length) =
      BitVec.ofNat 64 remaining := by
  rw [BitVec.add_comm]
  exact BitVec.sub_add_cancel _ _

theorem trim_index_address (pointer : BitVec 64) (length n : Nat) :
    pointer + BitVec.ofNat 64 (8 * length) - 8#64 +
        ((BitVec.ofNat 64 (n + 1) - BitVec.ofNat 64 length) <<< 3) =
      pointer + (BitVec.ofNat 64 n <<< 3) := by
  have shift (word : BitVec 64) : word <<< 3 = 8#64 * word := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change word * 8#64 = 8#64 * word
    exact BitVec.mul_comm _ _
  simp only [shift, BitVec.ofNat_mul, BitVec.ofNat_add, BitVec.mul_sub,
    BitVec.mul_add]
  arm_word_nf
  change pointer + (8#64 * BitVec.ofNat 64 length) - 8#64 +
      (8#64 * BitVec.ofNat 64 n + 8#64 - 8#64 * BitVec.ofNat 64 length) =
    pointer + 8#64 * BitVec.ofNat 64 n
  calc
    _ = (pointer + 8#64 * BitVec.ofNat 64 n) +
        (8#64 * BitVec.ofNat 64 length - 8#64 * BitVec.ofNat 64 length) +
        (8#64 - 8#64) := by
      simp only [BitVec.sub_eq_add_neg]
      ac_rfl
    _ = _ := by rw [BitVec.sub_self, BitVec.sub_self, BitVec.add_zero, BitVec.add_zero]

theorem trim_offset_step (bias : BitVec 64) (n : Nat) :
    bias - BitVec.ofNat 64 (8 * (n + 1)) + 8#64 =
      bias - BitVec.ofNat 64 (8 * n) := by
  rw [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add]
  apply BitVec.eq_sub_iff_add_eq.mpr
  calc
    _ = bias - (BitVec.ofNat 64 (8 * n) + BitVec.ofNat 64 8) +
        (BitVec.ofNat 64 (8 * n) + BitVec.ofNat 64 8) := by
      arm_word_nf
      ac_rfl
    _ = bias := BitVec.sub_add_cancel _ _

theorem trim_index_step (length n : Nat) :
    BitVec.ofNat 64 (n + 1) - BitVec.ofNat 64 length - 1#64 =
      BitVec.ofNat 64 n - BitVec.ofNat 64 length := by
  apply BitVec.sub_eq_iff_eq_add.mpr
  apply BitVec.sub_eq_iff_eq_add.mpr
  rw [BitVec.ofNat_add]
  calc
    _ = BitVec.ofNat 64 n + 1#64 := by arm_word_nf
    _ = (BitVec.ofNat 64 n - BitVec.ofNat 64 length + BitVec.ofNat 64 length) +
        1#64 := by rw [BitVec.sub_add_cancel]
    _ = _ := by ac_rfl

end SszArm.NatMulWord

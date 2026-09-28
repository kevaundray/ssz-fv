import SszArm.NatMulWordScanStages

namespace SszArm.NatMulWord

theorem trim_remaining_sum (length remaining : Nat) :
    BitVec.ofNat 64 length + (BitVec.ofNat 64 remaining - BitVec.ofNat 64 length) =
      BitVec.ofNat 64 remaining := by bv_omega

theorem trim_index_address (pointer : BitVec 64) (length n : Nat) :
    pointer + BitVec.ofNat 64 (8 * length) - 8#64 +
        ((BitVec.ofNat 64 (n + 1) - BitVec.ofNat 64 length) <<< 3) =
      pointer + (BitVec.ofNat 64 n <<< 3) := by bv_omega

theorem trim_offset_step (bias : BitVec 64) (n : Nat) :
    bias - BitVec.ofNat 64 (8 * (n + 1)) + 8#64 =
      bias - BitVec.ofNat 64 (8 * n) := by bv_omega

theorem trim_index_step (length n : Nat) :
    BitVec.ofNat 64 (n + 1) - BitVec.ofNat 64 length - 1#64 =
      BitVec.ofNat 64 n - BitVec.ofNat 64 length := by bv_omega

end SszArm.NatMulWord

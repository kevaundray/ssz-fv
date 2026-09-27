import SszArm.DelimitedArithmetic

namespace SszArm.Delimited

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The actual ORR (not an assumed u128 operation) computes the count low word.
The delimiter index occupies the three bits cleared by the byte-prefix shift. -/
theorem count_low_word (length highest : Nat)
    (physical : length < 2^64) (bit : highest < 8) :
    BitVec.ofNat 64 highest ||| (BitVec.ofNat 64 (length - 1) <<< 3) =
      BitVec.ofNat 64 (8 * (length - 1) + highest) := by
  have hprefix : length - 1 < 2^64 := by omega
  have shift : BitVec.ofNat 64 (length - 1) <<< 3 =
      BitVec.ofNat 64 (8 * (length - 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hprefix,
      Nat.shiftLeft_eq, Nat.mul_comm]
  rw [shift, BitVec.or_comm, ← BitVec.ofNat_or]
  have join : 8 * (length - 1) ||| highest = 8 * (length - 1) + highest :=
    (Nat.two_pow_add_eq_or_of_lt (i := 3) bit (length - 1)).symm
  rw [join]

/-- X23's shift is the high limb of the full mathematical count. -/
theorem count_high_word (length highest : Nat)
    (physical : length < 2^64) (bit : highest < 8) :
    (BitVec.ofNat 64 (length - 1) >>> 61).toNat =
      (8 * (length - 1) + highest) / 2^64 := by
  have hprefix : length - 1 < 2^64 := by omega
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hprefix,
    Nat.shiftRight_eq_div_pow, count_high length highest bit]

end SszArm.Delimited

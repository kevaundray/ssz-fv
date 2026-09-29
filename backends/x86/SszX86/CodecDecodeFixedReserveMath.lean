import SszX86.UintArenaMemory
import SszCodecDecodeCore

set_option autoImplicit false

namespace SszX86.CodecDecodeFixed
open SszNative

/-- The Value allocator clears four low bits, unlike the old limb allocator. -/
theorem value_mask_toNat (word : BitVec 64) :
    (word &&& ~~~(15 : BitVec 64)).toNat = word.toNat / 16 * 16 := by
  have mask : (~~~(15 : BitVec 64)) = BitVec.allOnes 64 <<< 4 := by decide
  rw [mask, ← BitVec.shiftLeft_ushiftRight, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  change (word.toNat / 16 * 16) % 2 ^ 64 = word.toNat / 16 * 16
  apply Nat.mod_eq_of_lt
  have := word.isLt
  omega

theorem value_mask_rounding (address : BitVec 64)
    (noOverflow : address.toNat + 15 < 2 ^ 64) :
    ((address + 15) &&& ~~~(15 : BitVec 64)).toNat =
      TypedArena.aligned CodecDecode.valueLayout address.toNat := by
  rw [value_mask_toNat, BitVec.toNat_add]
  change ((address.toNat + 15) % 2 ^ 64) / 16 * 16 =
    TypedArena.aligned CodecDecode.valueLayout address.toNat
  rw [Nat.mod_eq_of_lt noOverflow]
  rfl

theorem value_padding (address : BitVec 64)
    (noOverflow : address.toNat + 15 < 2 ^ 64) :
    (((address + 15) &&& ~~~(15 : BitVec 64)) - address).toNat =
      TypedArena.padding CodecDecode.valueLayout address.toNat := by
  have aligned := value_mask_rounding address noOverflow
  have lower := (TypedArena.aligned_bounds CodecDecode.valueLayout address.toNat).1
  have le : address ≤ (address + 15) &&& ~~~(15 : BitVec 64) := by
    change address.toNat ≤ ((address + 15) &&& ~~~(15 : BitVec 64)).toNat
    rw [aligned]
    exact lower
  rw [BitVec.toNat_sub_of_le le, aligned]
  rfl

/-- The MUL upper limb cannot wrap: a physical host count times 48 is below
2^70, so the 128-bit product observes the exact mathematical byte count. -/
theorem value_product (count : BitVec 64) :
    (count.setWidth 128 * 48#128).toNat = 48 * count.toNat := by
  have countBound := count.isLt
  have productBound : count.toNat * 48 < 2 ^ 128 := by omega
  rw [BitVec.toNat_mul,
    BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128)]
  change (count.toNat * 48) % 2 ^ 128 = 48 * count.toNat
  rw [Nat.mod_eq_of_lt productBound]
  omega

/-- The compiled MUL carry test followed by the signed-size test rejects
exactly the typed arena's positive-isize bound, including usize overflow. -/
theorem value_product_refusal (count : BitVec 64) :
    ((count.setWidth 128 * 48#128).extractLsb' 64 64 ≠ 0 ∨
      (count * 48#64).msb = true) ↔ 2 ^ 63 ≤ 48 * count.toNat := by
  have product := value_product count
  have countBound := count.isLt
  have productBound : 48 * count.toNat < 2 ^ 128 := by omega
  have highBound : 48 * count.toNat / 2 ^ 64 < 2 ^ 64 := by omega
  have highNat : ((count.setWidth 128 * 48#128).extractLsb' 64 64).toNat =
      48 * count.toNat / 2 ^ 64 := by
    rw [BitVec.extractLsb'_toNat, product, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt highBound
  have highZero : (count.setWidth 128 * 48#128).extractLsb' 64 64 = 0 ↔
      48 * count.toNat / 2 ^ 64 = 0 := by
    constructor
    · intro equal
      have numbers := congrArg BitVec.toNat equal
      simpa only [highNat, BitVec.toNat_zero] using numbers
    · intro equal
      apply BitVec.eq_of_toNat_eq
      simpa only [highNat, BitVec.toNat_zero] using equal
  rw [ne_eq, highZero]
  simp only [BitVec.msb_eq_decide, decide_eq_true_eq, BitVec.toNat_mul,
    BitVec.toNat_ofNat]
  omega

/-- For struct field slices the native unchecked SHL/LEA product is justified
by physical isize-sized slice storage, not a bound on logical descriptor Nats. -/
theorem struct_value_product (count : Nat) (physical : 24 * count < 2 ^ 63) :
    48 * count < 2 ^ 64 ∧
    ((BitVec.ofNat 64 count <<< 4) + (BitVec.ofNat 64 count <<< 4) * 2).toNat = 48 * count := by
  have countBound : count < 2 ^ 64 := by omega
  have shiftedBound : count * 16 < 2 ^ 64 := by omega
  have twiceBound : count * 16 * 2 < 2 ^ 64 := by omega
  have totalBound : count * 16 + count * 16 * 2 < 2 ^ 64 := by omega
  refine ⟨by omega, ?_⟩
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_eq_of_lt countBound]
  change ((count * 16) % 2 ^ 64 +
    ((count * 16) % 2 ^ 64 * 2) % 2 ^ 64) % 2 ^ 64 = 48 * count
  rw [Nat.mod_eq_of_lt shiftedBound, Nat.mod_eq_of_lt twiceBound,
    Nat.mod_eq_of_lt totalBound]
  omega

end SszX86.CodecDecodeFixed

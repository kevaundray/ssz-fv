import SszArm.DelimitedArithmetic
import SszArm.Udivti3Arithmetic

namespace SszArm.Delimited

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The addition Z flag observes the actual modular result. -/
theorem add_zero_flag (a b : BitVec 64) :
    (AddWithCarry a b 0#1).2.z = 1#1 ↔ a + b = 0#64 := by
  change (if (AddWithCarry a b 0#1).1 = 0#64 then 1#1 else 0#1) = 1#1 ↔ _
  rw [fst_AddWithCarry_eq_add]
  simp

/-- CMN/B.HI rejects strict overflow, preserving the endpoint equality used in
the native +7 alignment and +16 payload guards. -/
theorem cmn_hi (a b : BitVec 64) :
    ((AddWithCarry a b 0#1).2.c = 1#1 ∧ (AddWithCarry a b 0#1).2.z ≠ 1#1) ↔
      2^64 < a.toNat + b.toNat := by
  have carry : (AddWithCarry a b 0#1).2.c = 1#1 ↔ 2^64 ≤ a.toNat + b.toNat := by
    simpa [Udivti3.radix] using Udivti3.adc_carry a b 0#1
  constructor
  · rintro ⟨hc, hz⟩
    have bound := carry.mp hc
    have nonzero : a + b ≠ 0#64 := fun h => hz ((add_zero_flag a b).mpr h)
    bv_omega
  · intro bound
    refine ⟨carry.mpr (by omega), ?_⟩
    intro hz
    have zero := (add_zero_flag a b).mp hz
    bv_omega

/-- The AND mask clears exactly the low three bits, without a native decision
oracle and without requiring the value to fit isize. -/
theorem align_mask (x : BitVec 64) :
    (x &&& 18446744073709551608#64).toNat = (x.toNat / 8) * 8 := by
  rw [show 18446744073709551608#64 = (BitVec.allOnes 64 <<< 3) by decide,
    ← BitVec.shiftLeft_ushiftRight]
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have high := x.isLt
  omega

/-- The machine address/padding calculation equals Arena.aligned/padding once
its two preceding overflow branches have been passed. -/
theorem reservation_padding (address : BitVec 64)
    (rounding : address.toNat + 7 < 2^64) :
    let aligned := (address + 7#64) &&& 18446744073709551608#64
    aligned.toNat = SszNative.Arena.aligned address.toNat ∧
      (aligned - address).toNat = SszNative.Arena.padding address.toNat := by
  change ((address + 7#64) &&& 18446744073709551608#64).toNat =
      SszNative.Arena.aligned address.toNat ∧
    (((address + 7#64) &&& 18446744073709551608#64) - address).toNat =
      SszNative.Arena.padding address.toNat
  have add : (address + 7#64).toNat = address.toNat + 7 := by bv_omega
  have aligned : ((address + 7#64) &&& 18446744073709551608#64).toNat =
      SszNative.Arena.aligned address.toNat := by
    rw [align_mask, add]
    rfl
  refine ⟨aligned, ?_⟩
  have bounds := SszNative.Arena.aligned_bounds address.toNat
  rw [BitVec.toNat_sub, aligned]
  unfold SszNative.Arena.padding
  omega

/-- The native CMN constants are one more than the requested checked additions. -/
theorem rounding_guard (address : BitVec 64) :
    ¬ ((AddWithCarry address 8#64 0#1).2.c = 1#1 ∧
      (AddWithCarry address 8#64 0#1).2.z ≠ 1#1) ↔ address.toNat + 7 < 2^64 := by
  rw [cmn_hi]
  simp only [BitVec.toNat_ofNat]
  omega

theorem payload_guard (cursor : BitVec 64) :
    ¬ ((AddWithCarry cursor 17#64 0#1).2.c = 1#1 ∧
      (AddWithCarry cursor 17#64 0#1).2.z ≠ 1#1) ↔ cursor.toNat + 16 < 2^64 := by
  rw [cmn_hi]
  simp only [BitVec.toNat_ofNat]
  omega

end SszArm.Delimited

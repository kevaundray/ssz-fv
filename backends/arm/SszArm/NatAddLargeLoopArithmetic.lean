import SszArm.NatAddLoopMemory
import SszArm.Udivti3Arithmetic

namespace SszArm.NatAdd.LargeLoop

open SszNative

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def carryWord (left right : BitVec 64) : BitVec 64 :=
  if (AddWithCarry left right 0#1).2.c = 1#1 then 1#64 else 0#64

theorem carryWord_nat (left right : BitVec 64) :
    (carryWord left right).toNat = (left.toNat + right.toNat) / 2^64 := by
  have flag := Udivti3.adc_carry_nat left right 0#1
  have bound := (AddWithCarry left right 0#1).2.c.isLt
  by_cases h : (AddWithCarry left right 0#1).2.c = 1#1
  · simpa [carryWord, h, Udivti3.radix] using flag
  · have zero : (AddWithCarry left right 0#1).2.c = 0#1 := by bv_omega
    simpa [carryWord, h, zero, Udivti3.radix] using flag

/-- The machine first adds the incoming carry to the right word, then the
left word; this is exactly the native widened low word. -/
theorem add_low (left right : BitVec 64) (carry : Nat) :
    (BitVec.ofNat 64 carry + right) + left = (LimbAdd.step left right carry).1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [LimbAdd.step, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The two overflow bits aggregate to the one native outgoing carry. No
signed bound is imposed on either original operand or its physical length. -/
theorem add_carry (left right : BitVec 64) (carry : Nat) (hc : carry ≤ 1) :
    carryWord (BitVec.ofNat 64 carry) right +
      carryWord (BitVec.ofNat 64 carry + right) left =
      BitVec.ofNat 64 (LimbAdd.step left right carry).2 := by
  have hfirst := carryWord_nat (BitVec.ofNat 64 carry) right
  have hsecond := carryWord_nat (BitVec.ofNat 64 carry + right) left
  have hl := left.isLt
  have hr := right.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hfirst hsecond ⊢
  simp only [LimbAdd.step]
  omega

/-- The significant-width reservation consumes the carry even when the
original input lists contain arbitrarily many redundant high zeros. -/
theorem final_carry (left right : List (BitVec 64)) (count index carry : Nat)
    (hl : (Limbs.trim left).length ≤ count)
    (hr : (Limbs.trim right).length ≤ count)
    (hi : index ≤ count) (hc : carry ≤ 1) :
    (LimbAdd.loop (count + 1 - index) (left.drop index) (right.drop index) carry).2 = 0 := by
  rw [← SszNative.NatAdd.loop_trim_eq_native]
  apply LimbAdd.loop_carry_eq_zero
  · simp only [List.length_drop]; omega
  · simp only [List.length_drop]; omega
  · exact hc

end SszArm.NatAdd.LargeLoop

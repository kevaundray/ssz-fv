import SszArm.NatAddImpl
import SszNatAdd

namespace SszArm.NatAdd

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The compiler's OR/CMP #2 branch tests the two significant widths jointly. -/
theorem width_or_small (a b : BitVec 64) :
    (a ||| b).toNat < 2 ↔ a.toNat ≤ 1 ∧ b.toNat ≤ 1 := by
  rw [BitVec.toNat_or]
  constructor
  · intro small
    have left := Nat.left_le_or (n := a.toNat) (m := b.toNat)
    have right := Nat.right_le_or (n := a.toNat) (m := b.toNat)
    omega
  · intro small
    have bound := Nat.or_lt_two_pow (n := 1) (x := a.toNat) (y := b.toNat)
      (by omega) (by omega)
    exact bound

/-- Physical limb arrays bound the significant count, not signed arena capacity. -/
theorem count_physical (observe : Nat → Nat → Option Nat) (operand : SszNative.NatOperand)
    (input : operand.At observe) : operand.wordCount ≤ 2^61 := by
  have count := SszNative.Limbs.sigWords_le_length operand.words
  cases operand with
  | small word =>
    simp only [SszNative.NatOperand.words, List.length_cons, List.length_nil] at count
    exact Nat.le_trans count (by decide)
  | large pointer words =>
    have physical := input.2.2.1
    change SszNative.Limbs.sigWords words ≤ words.length at count
    change SszNative.Limbs.sigWords words ≤ 2^61
    omega

/-- The checked-add branch remains in the executed image, but cannot overflow
for any pair of caller-owned physical operand representations. -/
theorem allocated_count_physical (observe : Nat → Nat → Option Nat)
    (left right : SszNative.NatOperand) (hl : left.At observe) (hr : right.At observe) :
    SszNative.NatAdd.count left right + 1 < 2^64 := by
  have leftBound := count_physical observe left hl
  have rightBound := count_physical observe right hr
  simp only [SszNative.NatAdd.count]
  omega

end SszArm.NatAdd

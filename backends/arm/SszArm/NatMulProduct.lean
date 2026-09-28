import SszArm.NatMulArithmetic
import SszLimbMul

namespace SszArm.NatMulProduct

local notation "H" => (2 ^ 32 : Nat)
local notation "B" => (2 ^ 64 : Nat)

/-- The actual ARM unsigned-high lowering, including its 64-bit intermediates. -/
def high (a b : BitVec 64) : BitVec 64 :=
  let a0 := (a.setWidth 32).setWidth 64
  let a1 := a >>> 32
  let b0 := (b.setWidth 32).setWidth 64
  let b1 := b >>> 32
  let u := (a0 * b0) >>> 32
  let v := a1 * b0 + u
  let h := v >>> 32
  let w := a0 * b1 + (v.setWidth 32).setWidth 64
  let z := w >>> 32
  a1 * b1 + h + z

theorem lowHalf_toNat (a : BitVec 64) :
    ((a.setWidth 32).setWidth 64).toNat = a.toNat % H := by
  rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64), BitVec.toNat_setWidth]

theorem highHalf_toNat (a : BitVec 64) :
    (a >>> 32).toNat = a.toNat / H := by
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem digit_product_le (x y : Nat) (hx : x < H) (hy : y < H) :
    x * y ≤ (H - 1) * (H - 1) :=
  Nat.mul_le_mul (by omega) (by omega)

/-- Every partial product, both cross-product accumulators, and the final high
accumulator fit their actual machine width. Only the four 32-bit bounds enter. -/
theorem intermediate_bounds (a0 a1 b0 b1 : Nat)
    (ha0 : a0 < H) (ha1 : a1 < H) (hb0 : b0 < H) (hb1 : b1 < H) :
    let p := a0 * b0
    let v := a1 * b0 + p / H
    let w := a0 * b1 + v % H
    p < B ∧ a1 * b0 < B ∧ a0 * b1 < B ∧ a1 * b1 < B ∧
      v < B ∧ w < B ∧ a1 * b1 + v / H + w / H < B := by
  have hp := digit_product_le a0 b0 ha0 hb0
  have h10 := digit_product_le a1 b0 ha1 hb0
  have h01 := digit_product_le a0 b1 ha0 hb1
  have h11 := digit_product_le a1 b1 ha1 hb1
  dsimp only
  omega

private theorem schoolbook (a0 a1 b0 b1 : Nat) :
    (a0 + H * a1) * (b0 + H * b1) =
      a0 * b0 + H * (a1 * b0) + H * (a0 * b1) + B * (a1 * b1) := by
  calc
    _ = a0 * b0 + H * (a1 * b0) + H * (a0 * b1) +
        (H * H) * (a1 * b1) := by
      simp only [Nat.add_mul, Nat.mul_add]
      ac_rfl
    _ = _ := by rfl

/-- Quotient of the ordinary product after the two cross-product carries.
This is a decomposition theorem, not an alternative multiplication model. -/
theorem high_quotient (a0 a1 b0 b1 : Nat) :
    let p := a0 * b0
    let v := a1 * b0 + p / H
    let w := a0 * b1 + v % H
    a1 * b1 + v / H + w / H =
      ((a0 + H * a1) * (b0 + H * b1)) / B := by
  have hp := Nat.mod_add_div (a0 * b0) H
  have hv := Nat.mod_add_div (a1 * b0 + (a0 * b0) / H) H
  have hw := Nat.mod_add_div (a0 * b1 +
    (a1 * b0 + (a0 * b0) / H) % H) H
  rw [schoolbook]
  dsimp only
  omega

/-- The lowering does not merely agree modulo 64 bits: its natural value is
exactly the upper half of the full unsigned 64-by-64 product. -/
theorem high_toNat (a b : BitVec 64) :
    (high a b).toNat = a.toNat * b.toNat / B := by
  have ha := a.isLt
  have hb := b.isLt
  have ha0 : a.toNat % H < H := Nat.mod_lt _ (by decide)
  have hb0 : b.toNat % H < H := Nat.mod_lt _ (by decide)
  have ha1 : a.toNat / H < H := by omega
  have hb1 : b.toNat / H < H := by omega
  have ha0wide : a.toNat % H < B := by omega
  have hb0wide : b.toNat % H < B := by omega
  rcases intermediate_bounds (a.toNat % H) (a.toNat / H)
    (b.toNat % H) (b.toNat / H) ha0 ha1 hb0 hb1 with
    ⟨hp, h10, h01, h11, hv, hw, hh⟩
  have quotient := high_quotient (a.toNat % H) (a.toNat / H)
    (b.toNat % H) (b.toNat / H)
  simp only [Nat.mod_add_div] at quotient
  have hvhalf :
      ((a.toNat / H) * (b.toNat % H) +
        ((a.toNat % H) * (b.toNat % H)) / H) % H < B := by omega
  have hfirst : (a.toNat / H) * (b.toNat / H) +
      ((a.toNat / H) * (b.toNat % H) +
        ((a.toNat % H) * (b.toNat % H)) / H) / H < B := by omega
  simp only [high, BitVec.toNat_add, BitVec.toNat_mul,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_setWidth]
  simp only [Nat.mod_eq_of_lt ha0wide, Nat.mod_eq_of_lt hb0wide]
  simp only [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt h10,
    Nat.mod_eq_of_lt h01, Nat.mod_eq_of_lt h11]
  simp only [Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hvhalf]
  simp only [Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hfirst, Nat.mod_eq_of_lt hh]
  exact quotient

theorem high_eq (a b : BitVec 64) :
    high a b = BitVec.ofNat 64 (a.toNat * b.toNat / B) := by
  apply BitVec.eq_of_toNat_eq
  rw [high_toNat, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (by rw [← high_toNat]; exact (high a b).isLt)).symm

theorem low_eq (a b : BitVec 64) :
    a * b = BitVec.ofNat 64 (a.toNat * b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]

/-- Exact low/high conservation used when adding the old limb and carry. -/
theorem product_value (a b : BitVec 64) :
    (a * b).toNat + B * (high a b).toNat = a.toNat * b.toNat := by
  rw [BitVec.toNat_mul, high_toNat]
  exact Nat.mod_add_div _ B

/-- The zero-accumulator case of the already checked shared multiplication step. -/
theorem step_zero (a b : BitVec 64) :
    SszNative.LimbMul.step a b 0#64 0 = (a * b, (high a b).toNat) := by
  simp only [SszNative.LimbMul.step, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.add_zero, low_eq, high_toNat]

end SszArm.NatMulProduct

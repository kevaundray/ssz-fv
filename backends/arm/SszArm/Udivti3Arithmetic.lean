import SszArm.Udivti3
import SszDivision
import SszDivisionBits

namespace SszArm.Udivti3

open BitVec
open SszNative

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

abbrev radix : Nat := 18446744073709551616
abbrev halfRadix : Nat := 9223372036854775808

-- The variable multiplier prevents reduction through a 2^64-sized recursion.
def join (lo hi : BitVec 64) : Nat := radix * hi.toNat + lo.toNat

theorem join_eq (lo hi : BitVec 64) : join lo hi = hi.toNat * radix + lo.toNat := by
  simp only [join, Nat.mul_comm]

def numerator (s : ArmState) : Nat := join (r (.GPR 0) s) (r (.GPR 1) s)
def divisor (s : ArmState) : Nat := join (r (.GPR 2) s) (r (.GPR 3) s)

theorem join_lt (lo hi : BitVec 64) : join lo hi < 2^128 := by
  have hl := lo.isLt
  have hh := hi.isLt
  dsimp [join, radix]
  omega

theorem join_lt_iff (al ah bl bh : BitVec 64) :
    join al ah < join bl bh ↔
      ah.toNat < bh.toNat ∨ ah = bh ∧ al.toNat < bl.toNat := by
  have ha := al.isLt
  have hb := bl.isLt
  have he : ah = bh ↔ ah.toNat = bh.toNat := ⟨congrArg BitVec.toNat, BitVec.eq_of_toNat_eq⟩
  rw [he]
  dsimp [join, radix]
  omega

/-- General ADC facts proved from the widened sum, not from an oracle. -/
theorem adc_value (a b : BitVec 64) (c : BitVec 1) :
    (AddWithCarry a b c).1 = a + b + c.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [AddWithCarry, BitVec.toNat_setWidth,
    BitVec.toNat_add]
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  omega

theorem adc_carry (a b : BitVec 64) (c : BitVec 1) :
    (AddWithCarry a b c).2.c = 1#1 ↔ radix ≤ a.toNat + b.toNat + c.toNat := by
  simp only [AddWithCarry, make_pstate, radix]
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  split <;> simp_all <;> bv_omega

theorem adc_carry_nat (a b : BitVec 64) (c : BitVec 1) :
    (AddWithCarry a b c).2.c.toNat = (a.toNat + b.toNat + c.toNat) / radix := by
  have h := adc_carry a b c
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have ho := (AddWithCarry a b c).2.c.isLt
  dsimp [radix] at h ⊢
  by_cases hx : (AddWithCarry a b c).2.c = 1#1 <;> simp_all <;> bv_omega

theorem cmp_carry (a b : BitVec 64) :
    (AddWithCarry a (~~~b) 1#1).2.c = 1#1 ↔ b.toNat ≤ a.toNat := by
  rw [adc_carry]
  simp only [BitVec.toNat_not, BitVec.toNat_ofNat, radix]
  have hb := b.isLt
  omega

theorem cmp_zero (a b : BitVec 64) :
    (AddWithCarry a (~~~b) 1#1).2.z = 1#1 ↔ a = b := by
  have hv : (AddWithCarry a (~~~b) 1#1).1 = a - b := by
    simp only [fst_AddWithCarry_eq_sub_neg, BitVec.not_not]
  change (if (AddWithCarry a (~~~b) 1#1).1 = 0#64 then 1#1 else 0#1) = 1#1 ↔ _
  rw [hv]
  by_cases h : a = b
  · simp [h]
  · have hz : a - b ≠ 0#64 := by bv_omega
    simp [h, hz]

@[simp] theorem cmp_one_zero (a : BitVec 64) :
    (AddWithCarry a 18446744073709551614#64 1#1).2.z = 1#1 ↔ a = 1#64 :=
  cmp_zero a 1#64

theorem eq_iff_order (a b : BitVec 64) :
    a = b ↔ ¬a.toNat < b.toNat ∧ ¬b.toNat < a.toNat := by
  have he : a = b ↔ a.toNat = b.toNat := ⟨congrArg BitVec.toNat, BitVec.eq_of_toNat_eq⟩
  rw [he]
  omega

theorem cmp_nonzero (a b : BitVec 64) :
    (AddWithCarry a (~~~b) 1#1).2.z = 0#1 ↔ a ≠ b := by
  have h := cmp_zero a b
  have hz := (AddWithCarry a (~~~b) 1#1).2.z.isLt
  by_cases he : a = b <;> simp_all <;> bv_omega

theorem cmp_high (a b : BitVec 64) :
    ((AddWithCarry a (~~~b) 1#1).2.c = 1#1 ∧
      (AddWithCarry a (~~~b) 1#1).2.z = 0#1) ↔ b.toNat < a.toNat := by
  rw [cmp_carry, cmp_nonzero]
  have he : a = b ↔ a.toNat = b.toNat := ⟨congrArg BitVec.toNat, BitVec.eq_of_toNat_eq⟩
  simp only [ne_eq, he]
  omega

/-- The consumed input bit is the carry of the input-word doubling. -/
def topBit (x : BitVec 64) : Nat := x.toNat / halfRadix

theorem topBit_lt (x : BitVec 64) : topBit x < 2 := by
  have hx := x.isLt
  dsimp [topBit, halfRadix]
  omega

theorem double_carry (x : BitVec 64) :
    (AddWithCarry x x 0#1).2.c.toNat = topBit x := by
  rw [adc_carry_nat]
  simp only [BitVec.toNat_ofNat]
  dsimp [topBit, halfRadix, radix]
  omega

theorem double_carry_word (x : BitVec 64) :
    (AddWithCarry x x 0#1).2.c.setWidth 64 = BitVec.ofNat 64 (topBit x) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, double_carry, Nat.mod_eq_of_lt
    (show topBit x < radix from Nat.lt_trans (topBit_lt x) (by decide))]

/-- Unconsumed low bits, aligned with their next bit at bit 63. -/
def pending (n : BitVec 64) (k : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (n.toNat * 2^(64-k))

theorem pending_full (n : BitVec 64) : pending n 64 = n := by
  simp [pending]

/-- Cancel the alignment power of two when extracting the next input bit. -/
theorem pending_bit (n : BitVec 64) (k : Nat) (hk : k < 64) :
    topBit (pending n (k+1)) = (n.toNat / 2^k) % 2 := by
  have he : k + (64-(k+1)) = 63 := by omega
  have hp : 2^63 = 2^k * 2^(64-(k+1)) := by rw [← Nat.pow_add, he]
  change (n.toNat * 2^(64-(k+1)) % (2^63 * 2)) / 2^63 = _
  rw [Nat.mod_mul_right_div_self, hp,
    Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _)]

theorem pending_next (n : BitVec 64) (k : Nat) (hk : k < 64) :
    pending n (k+1) + pending n (k+1) = pending n k := by
  have he : 64-k = (64-(k+1))+1 := by omega
  unfold pending
  rw [← BitVec.ofNat_add]
  congr 1
  rw [he, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]

theorem prefix_bound_step (w k v bit : Nat) (hk : k < w)
    (hv : v < 2^(w-(k+1))) (hb : bit < 2) : 2*v+bit < 2^(w-k) := by
  have he : w-k = (w-(k+1))+1 := by omega
  rw [he, Nat.pow_succ]
  omega

theorem prefix_bound_radix (k q : Nat) (hk : k ≤ 64)
    (hq : q < 2^(64-k)) : q < radix := by
  have hm : 2^(64-k) ≤ 2^64 := Nat.pow_le_pow_right (by decide) (by omega)
  dsimp [radix]
  omega

/-- Both halves of the tentative wide remainder, including the low-word carry. -/
theorem wide_double (lo hi x : BitVec 64)
    (hb : 2 * join lo hi + topBit x < 2^128) :
    let c := (AddWithCarry x x 0#1).2.c
    let low := AddWithCarry lo lo c
    join low.1 (AddWithCarry hi hi low.2.c).1 = 2 * join lo hi + topBit x := by
  dsimp only
  have hc := double_carry x
  have hlc := adc_carry_nat lo lo (AddWithCarry x x 0#1).2.c
  have hhi := hi.isLt
  have hlo := lo.isLt
  have hbit := topBit_lt x
  simp only [adc_value, join, radix, BitVec.toNat_add, BitVec.toNat_setWidth] at *
  omega

/-- `SUBS`/`SBC` implements full-width subtraction, including its borrow. -/
theorem wide_subtract (lo hi dl dh : BitVec 64) (hle : join dl dh ≤ join lo hi) :
    join (AddWithCarry lo (~~~dl) 1#1).1
      (AddWithCarry hi (~~~dh) (AddWithCarry lo (~~~dl) 1#1).2.c).1 =
      join lo hi - join dl dh := by
  have hc := adc_carry_nat lo (~~~dl) 1#1
  have hlo := lo.isLt
  have hhi := hi.isLt
  have hdl := dl.isLt
  have hdh := dh.isLt
  simp only [adc_value, join, radix, BitVec.toNat_add, BitVec.toNat_setWidth,
    BitVec.toNat_not, BitVec.toNat_ofNat] at *
  omega

/-- Carry-aware restoring subtraction on one 64-bit remainder. -/
theorem word_step (r d x : BitVec 64) (hr : r.toNat < d.toNat) :
    let c := (AddWithCarry x x 0#1).2.c
    let t := (AddWithCarry r r c).1
    (if radix ≤ 2*r.toNat+topBit x ∨ d.toNat ≤ t.toNat then t-d else t).toNat =
      (Division.step d.toNat (topBit x) 0 r.toNat).2 := by
  have hbit := topBit_lt x
  have hvalue : (AddWithCarry r r (AddWithCarry x x 0#1).2.c).1 =
      DivisionBits.stepLo r (topBit x) := by
    rw [adc_value, double_carry_word]
    exact DivisionBits.stepLo_eq (by decide) r (topBit x) hbit
  dsimp only
  rw [hvalue]
  have ht := DivisionBits.remainderStep_toNat (by decide) r d (topBit x) hbit hr
  simpa only [DivisionBits.remainderStep, DivisionBits.stepTake, DivisionBits.stepCarry,
    DivisionBits.stepNat, Division.step, radix, Bool.or_eq_true, decide_eq_true_eq,
    apply_ite] using ht

end SszArm.Udivti3

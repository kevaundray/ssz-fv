import SszX86.Udivti3Impl
import SszDivision
import SszDivisionBits

namespace SszX86.Udivti3

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

abbrev radix : Nat := 18446744073709551616

def value (lo hi : BitVec 64) : Nat := hi.toNat * radix + lo.toNat

def bit (x : BitVec 64) : Nat := 2 * x.toNat / radix

@[simp] theorem value_zero_high (x : BitVec 64) : value x 0 = x.toNat := by
  simp [value]

theorem value_lt (lo hi : BitVec 64) : value lo hi < radix * radix := by
  have := lo.isLt
  have := hi.isLt
  dsimp [value, radix]
  omega

theorem bit_lt (x : BitVec 64) : bit x < 2 := by
  have := x.isLt
  dsimp [bit, radix]
  omega

def subFlags (a b : BitVec 64) : StatusFlags :=
  let v := a - b
  .from_result v {
    cf := v.unsigned != a.unsigned - b.unsigned
    af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned
    of := v.signed != a.signed - b.signed }

def addFlags (a b : BitVec 64) : StatusFlags :=
  let v := a + b
  .from_result v {
    cf := v.unsigned != a.unsigned + b.unsigned
    af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned
    of := v.signed != a.signed + b.signed }

def adcFlags (a b : BitVec 64) (c : Bool) : StatusFlags :=
  let v := a + b + BitVec.ofNat 64 c.toNat
  .from_result v {
    cf := v.unsigned != a.unsigned + b.unsigned + (c.toNat : Int)
    af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned + (c.toNat : Int)
    of := v.signed != a.signed + b.signed + (c.toNat : Int) }

@[simp] theorem subFlags_cf (a b : BitVec 64) :
    (subFlags a b).cf = decide (a.toNat < b.toNat) := by
  apply Bool.eq_iff_iff.mpr
  simp only [subFlags, StatusFlags.from_result, bne_iff_ne,
    decide_eq_true_eq, BitVec.unsigned]
  have := a.isLt
  have := b.isLt
  simp only [BitVec.toNat_sub]
  omega

@[simp] theorem subFlags_zf (a b : BitVec 64) :
    (subFlags a b).zf = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [subFlags, StatusFlags.from_result, beq_iff_eq, decide_eq_true_eq]
  change a - b = 0#64 ↔ a = b
  constructor
  · intro h
    have ha := congrArg (fun v : BitVec 64 => v + b) h
    simpa only [BitVec.sub_add_cancel, BitVec.zero_add] using ha
  · rintro rfl
    exact BitVec.sub_self _

@[simp] theorem addFlags_cf (a b : BitVec 64) :
    (addFlags a b).cf = decide (radix ≤ a.toNat + b.toNat) := by
  apply Bool.eq_iff_iff.mpr
  simp only [addFlags, StatusFlags.from_result, bne_iff_ne,
    decide_eq_true_eq, BitVec.unsigned, BitVec.toNat_add]
  have := a.isLt
  have := b.isLt
  dsimp [radix]
  omega

@[simp] theorem adcFlags_cf (a b : BitVec 64) (c : Bool) :
    (adcFlags a b c).cf = decide (radix ≤ a.toNat + b.toNat + c.toNat) := by
  apply Bool.eq_iff_iff.mpr
  cases c <;>
    simp [adcFlags, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add,
      BitVec.toNat_ofNat, radix] <;>
    have := a.isLt <;> have := b.isLt <;> omega

@[simp] theorem double_carry (x : BitVec 64) :
    (addFlags x x).cf.toNat = bit x := by
  rw [addFlags_cf]
  have := x.isLt
  unfold bit
  by_cases h : radix ≤ x.toNat + x.toNat <;> simp [h] <;> dsimp [radix] at * <;> omega

/-- Raw semantic flag expressions, used before folding a symbolic state. -/
@[simp] theorem cf_sub (a b : BitVec 64) :
    ((a - b).unsigned != a.unsigned - b.unsigned) = decide (a.toNat < b.toNat) :=
  subFlags_cf a b

@[simp] theorem zf_sub (a b : BitVec 64) :
    (a - b == 0#64) = decide (a = b) := subFlags_zf a b

@[simp] theorem cf_add (a b : BitVec 64) :
    ((a + b).unsigned != a.unsigned + b.unsigned) =
      decide (radix ≤ a.toNat + b.toNat) := addFlags_cf a b

@[simp] theorem cf_adc (a b : BitVec 64) (c : Bool) :
    ((a + b + BitVec.ofNat 64 c.toNat).unsigned !=
      a.unsigned + b.unsigned + (c.toNat : Int)) =
        decide (radix ≤ a.toNat + b.toNat + c.toNat) := adcFlags_cf a b c

/-- Numeric form of the word-loop ADC, including its carry-out. -/
theorem word_adc (x r : BitVec 64) :
    r + r + BitVec.ofNat 64 (addFlags x x).cf.toNat =
      SszNative.DivisionBits.stepLo r (bit x) ∧
    (adcFlags r r (addFlags x x).cf).cf =
      SszNative.DivisionBits.stepCarry r (bit x) := by
  constructor
  · rw [double_carry]
    exact SszNative.DivisionBits.stepLo_eq (by decide) r (bit x) (bit_lt x)
  · simp only [adcFlags_cf, double_carry, SszNative.DivisionBits.stepCarry,
      SszNative.DivisionBits.stepNat, Nat.two_mul]

/-- The unsigned lexicographic branch is precisely comparison of the two limbs. -/
theorem value_lt_iff (al ah bl bh : BitVec 64) :
    value al ah < value bl bh ↔
      ah.toNat < bh.toNat ∨ (ah = bh ∧ al.toNat < bl.toNat) := by
  have := al.isLt
  have := bl.isLt
  have he : ah = bh ↔ ah.toNat = bh.toNat :=
    ⟨congrArg BitVec.toNat, BitVec.eq_of_toNat_eq⟩
  simp only [he, value, radix]
  omega

theorem value_le_iff (al ah bl bh : BitVec 64) :
    value al ah ≤ value bl bh ↔
      ah.toNat ≤ bh.toNat ∧ (bh = ah → al.toNat ≤ bl.toNat) := by
  rw [← Nat.not_lt, value_lt_iff]
  simp only [not_or, not_and, Nat.not_lt]

/-- Both ADCs in the wide loop are one ordinary 128-bit left shift.
The bound is obtained from the consumed-input invariant, not assumed of inputs. -/
theorem wide_adc (x lo hi : BitVec 64)
    (h : 2 * value lo hi + bit x < radix * radix) :
    value
      (lo + lo + BitVec.ofNat 64 (addFlags x x).cf.toNat)
      (hi + hi + BitVec.ofNat 64 (adcFlags lo lo (addFlags x x).cf).cf.toNat) =
      2 * value lo hi + bit x := by
  have hb := bit_lt x
  have hl := lo.isLt
  have hh := hi.isLt
  rw [adcFlags_cf, double_carry]
  by_cases hc : radix ≤ lo.toNat + lo.toNat + bit x
  all_goals
    simp [hc, value, BitVec.toNat_add, BitVec.toNat_ofNat, radix] at h ⊢
    dsimp [radix] at hc
    omega

/-- SUB followed by SBB subtracts the complete divisor, including low-limb borrow. -/
theorem wide_sub (al ah bl bh : BitVec 64) (h : value bl bh ≤ value al ah) :
    value (al - bl)
      (ah - bh - BitVec.ofNat 64 (subFlags al bl).cf.toNat) =
      value al ah - value bl bh := by
  have := al.isLt
  have := ah.isLt
  have := bl.isLt
  have := bh.isLt
  rw [subFlags_cf]
  by_cases hc : al.toNat < bl.toNat
  all_goals
    simp [hc, value, BitVec.toNat_sub, BitVec.toNat_ofNat, radix] at h ⊢
    omega

/-- Quotient extraction from the division invariant at count zero. -/
theorem quotient_of_conservation (d q r n : Nat) (hd : 0 < d)
    (hr : r < d) (he : q * d + r = n) : q = n / d := by
  subst n
  rw [Nat.add_comm, Nat.add_mul_div_right r q hd, Nat.div_eq_of_lt hr, Nat.zero_add]

end SszX86.Udivti3

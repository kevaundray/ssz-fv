import SszIndicesArithmetic

set_option autoImplicit false

namespace SszArm.Indices.Rebase

open SszNative (NatOperand)
open SszNative.Indices

/-- The two-word quotient/remainder computation in the linked entry computes
exactly this count. This identity does not assume bits fits a machine word. -/
theorem increment_count (bits : Nat) :
    (bits + 1) / 64 + (if (bits + 1) % 64 = 0 then 0 else 1) =
      bits / 64 + 1 := by
  have before := Nat.mod_add_div bits 64
  have after := Nat.mod_add_div (bits + 1) 64
  have beforeBound := Nat.mod_lt bits (by decide : 0 < 64)
  have afterBound := Nat.mod_lt (bits + 1) (by decide : 0 < 64)
  split <;> omega

/-- Checked usize conversion is retained, rather than replaced with a bound on
the logical Nat operand or an unchecked low-word cast. -/
theorem checked_count (bits : Nat) :
    wordCount (bits + 1) =
      if bits / 64 + 1 < 2^64 then .ok (bits / 64 + 1) else .error scratch := by
  unfold wordCount
  rw [increment_count]

/-- Even a u128 input whose addition succeeds can fail the subsequent usize
conversion. These are ordered tests in the linked original-entry prefix. -/
theorem checked_plan (index : NatOperand) (bits base capacity used : Nat) :
    rebase index bits base capacity used =
      if bits + 1 < 2^128 then
        if bits / 64 + 1 < 2^64 then
          makeNat (bits / 64 + 1) base capacity used (fun i =>
            (word index i &&& rangeWord i 0 bits) ||| rangeWord i bits (bits + 1))
        else unchanged used (.error scratch)
      else unchanged used (.error scratch) := by
  unfold rebase
  rw [checked_count]
  split
  · split <;> rfl
  · rfl

/-- The checked conversion rejects precisely the last full 64-bit limb index
and everything beyond it; no wrapping count is passed to make_nat. -/
theorem count_fits_iff (bits : Nat) :
    bits / 64 + 1 < 2^64 ↔ bits < 64 * (2^64 - 1) := by
  omega

/-- Once the physical host count fits, the earlier u128 increment cannot have
overflowed. This implication permits eliminating unreachable error branches,
not changing their source precedence. -/
theorem count_fits_increment (bits : Nat) (fits : bits / 64 + 1 < 2^64) :
    bits + 1 < 2^128 := by
  have bounded := (count_fits_iff bits).mp fits
  omega

/-- An overflowing u128 input is rejected before any arena access or fill. -/
theorem overflow_unchanged (index : NatOperand) (bits base capacity used : Nat)
    (overflow : 2^128 ≤ bits + 1) :
    rebase index bits base capacity used = unchanged used (.error scratch) := by
  simp only [rebase, show ¬ bits + 1 < 2^128 by omega, ↓reduceIte]

/-- A failed usize conversion likewise records no arithmetic allocation event. -/
theorem oversized_unchanged (index : NatOperand) (bits base capacity used : Nat)
    (oversized : 64 * (2^64 - 1) ≤ bits) :
    rebase index bits base capacity used = unchanged used (.error scratch) := by
  rw [checked_plan]
  have count : ¬ bits / 64 + 1 < 2^64 := by
    rw [count_fits_iff]
    omega
  split <;> simp only [count, ↓reduceIte]

end SszArm.Indices.Rebase

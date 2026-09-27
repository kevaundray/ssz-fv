import Std

set_option autoImplicit false

namespace SszNative.DivisionBits

section

variable {w : Nat}

/-- The tentative restoring-division remainder before subtraction. -/
def stepNat (r : BitVec w) (bit : Nat) : Nat :=
  2 * r.toNat + bit

/-- The low-width bitvector that stores the tentative remainder. -/
def stepLo (r : BitVec w) (bit : Nat) : BitVec w :=
  BitVec.ofNat w (stepNat (w := w) r bit)

/-- Carry out of the widened `2 * r + bit` sum. -/
def stepCarry (r : BitVec w) (bit : Nat) : Bool :=
  decide (2 ^ w ≤ stepNat (w := w) r bit)

/-- Whether the restoring step subtracts the divisor. -/
def stepTake (r d : BitVec w) (bit : Nat) : Bool :=
  stepCarry (w := w) r bit || decide (d.toNat ≤ (stepLo (w := w) r bit).toNat)

/-- The modeled restoring-division remainder update. -/
def remainderStep (r d : BitVec w) (bit : Nat) : BitVec w :=
  if stepTake (w := w) r d bit then stepLo (w := w) r bit - d else stepLo (w := w) r bit

theorem stepTake_iff (_hw : 0 < w) (r d : BitVec w) (bit : Nat) (_hbit : bit < 2) :
    stepTake (w := w) r d bit = true ↔ d.toNat ≤ stepNat (w := w) r bit := by
  unfold stepTake stepCarry stepLo stepNat
  by_cases hc : 2 ^ w ≤ 2 * r.toNat + bit
  · have hd : d.toNat ≤ 2 * r.toNat + bit := by omega
    constructor
    · intro _
      exact hd
    · intro _
      simp [hc]
  · have hlt : 2 * r.toNat + bit < 2 ^ w := Nat.lt_of_not_ge hc
    have hlo : (BitVec.ofNat w (2 * r.toNat + bit)).toNat = 2 * r.toNat + bit := by
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    constructor
    · intro h
      simpa [hc, hlo] using h
    · intro h
      simpa [hc, hlo] using h

/-- The modeled restoring step computes the natural-number formula expected by the division loop. -/
theorem remainderStep_toNat (hw : 0 < w) (r d : BitVec w) (bit : Nat)
    (hbit : bit < 2) (hrd : r.toNat < d.toNat) :
    (remainderStep (w := w) r d bit).toNat =
      if d.toNat ≤ stepNat (w := w) r bit then stepNat (w := w) r bit - d.toNat else
        stepNat (w := w) r bit := by
  have ht : stepNat r bit = 2 * r.toNat + bit := rfl
  have hdB := d.isLt
  have htB : stepNat r bit < 2 * 2 ^ w := by omega
  have hsmall : stepNat r bit - d.toNat < 2 ^ w := by omega
  unfold remainderStep
  by_cases hd : d.toNat ≤ stepNat r bit
  · have htake := (stepTake_iff hw r d bit hbit).2 hd
    simp only [htake, hd, ↓reduceIte]
    rw [BitVec.toNat_sub]
    change (2 ^ w - d.toNat + stepNat r bit % 2 ^ w) % 2 ^ w =
      stepNat r bit - d.toNat
    by_cases hc : 2 ^ w ≤ stepNat r bit
    · have hmod : stepNat r bit % 2 ^ w = stepNat r bit - 2 ^ w := by
        rw [Nat.mod_eq_sub_mod hc, Nat.mod_eq_of_lt (by omega)]
      rw [hmod, show 2 ^ w - d.toNat + (stepNat r bit - 2 ^ w) =
        stepNat r bit - d.toNat by omega, Nat.mod_eq_of_lt hsmall]
    · rw [Nat.mod_eq_of_lt (Nat.lt_of_not_ge hc)]
      rw [show 2 ^ w - d.toNat + stepNat r bit =
        2 ^ w + (stepNat r bit - d.toNat) by omega]
      simp [Nat.mod_eq_of_lt hsmall]
  · have hnot : ¬ stepTake r d bit = true := by
      intro htake
      exact hd ((stepTake_iff hw r d bit hbit).1 htake)
    simp only [hnot, hd, ↓reduceIte]
    change stepNat r bit % 2 ^ w = stepNat r bit
    exact Nat.mod_eq_of_lt (by omega)

/-- The modeled restoring step always leaves a remainder strictly below the divisor. -/
theorem remainderStep_lt (hw : 0 < w) (r d : BitVec w) (bit : Nat)
    (hbit : bit < 2) (hrd : r.toNat < d.toNat) :
    (remainderStep (w := w) r d bit).toNat < d.toNat := by
  rw [remainderStep_toNat hw r d bit hbit hrd]
  split <;> dsimp [stepNat] at * <;> omega

/-- The widened arithmetic sum matches the low-width model used by the restoring step. -/
theorem stepLo_eq (_hw : 0 < w) (r : BitVec w) (bit : Nat) (_hbit : bit < 2) :
    r + r + BitVec.ofNat w bit = stepLo (w := w) r bit := by
  apply BitVec.eq_of_toNat_eq
  simp only [stepLo, stepNat, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod,
    Nat.mod_add_mod]
  simp [Nat.two_mul, Nat.add_comm]

end

end SszNative.DivisionBits

import SszNatDivision
import SszNatArithmeticMemory

set_option autoImplicit false

namespace SszNative

/-- Significant width, not physical padding, determines representability. -/
theorem NatOperand.wordCount_le_iff_value_lt (operand : NatOperand) (count : Nat) :
    operand.wordCount ≤ count ↔ operand.value < 2 ^ (64 * count) := by
  constructor
  · intro fits
    have upper := Limbs.value_lt (Limbs.trim operand.words)
    rw [Limbs.trim_value, Limbs.trim_length] at upper
    exact Nat.lt_of_lt_of_le upper
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 64 fits))
  · intro bound
    by_cases fits : operand.wordCount ≤ count
    · exact fits
    · have nonempty : Limbs.trim operand.words ≠ [] := by
        intro empty
        have length := Limbs.trim_length operand.words
        rw [empty] at length
        change 0 = operand.wordCount at length
        omega
      have lower := Limbs.canonical_ge_pow (Limbs.trim operand.words)
        (Limbs.trim_canonical operand.words) nonempty
      rw [Limbs.trim_value, Limbs.trim_length] at lower
      have powers : 2 ^ (64 * count) ≤ 2 ^ (64 * (operand.wordCount - 1)) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      exact False.elim (Nat.not_lt_of_ge (Nat.le_trans powers lower) bound)

namespace NatNarrow

/-- Native to_u128. The existing wideValue_native theorem gives its two-load,
zero-extended word implementation without imposing canonical physical input. -/
def toU128 (operand : NatOperand) : Option (BitVec 128) :=
  if operand.wordCount ≤ 2 then some (NatDivision.wideValue operand) else none

/-- codec::exact compares through cmp_usize/cmp_u128, not through a truncated
64-bit cast. Failure retains the original expected operand in the error. -/
def runExact (expected : NatOperand) (actual : BitVec 64) : Bool :=
  match toU128 expected with
  | none => false
  | some value => decide (value = actual.setWidth 128)

theorem toU128_some_iff (operand : NatOperand) (value : BitVec 128) :
    toU128 operand = some value ↔ value.toNat = operand.value := by
  constructor
  · intro result
    unfold toU128 at result
    split at result
    · rename_i fits
      cases result
      exact NatDivision.wideValue_toNat operand fits
    · cases result
  · intro equal
    have bound : operand.value < 2 ^ 128 := equal ▸ value.isLt
    have fits : operand.wordCount ≤ 2 :=
      (operand.wordCount_le_iff_value_lt 2).2 bound
    have same : NatDivision.wideValue operand = value := by
      apply BitVec.eq_of_toNat_eq
      exact (NatDivision.wideValue_toNat operand fits).trans equal.symm
    simp only [toU128, fits, ↓reduceIte, same]

theorem toU128_none_iff (operand : NatOperand) :
    toU128 operand = none ↔ 2 ^ 128 ≤ operand.value := by
  rw [toU128]
  by_cases fits : operand.wordCount ≤ 2
  · have bound := NatDivision.value_lt_128 operand fits
    simp only [fits, ↓reduceIte, Option.some_ne_none, false_iff]
    omega
  · have bound : ¬operand.value < 2 ^ 128 := by
      intro bound
      exact fits ((operand.wordCount_le_iff_value_lt 2).2 bound)
    simp only [fits, ↓reduceIte, true_iff]
    omega

theorem runExact_iff (expected : NatOperand) (actual : BitVec 64) :
    runExact expected actual = true ↔ expected.value = actual.toNat := by
  cases result : toU128 expected with
  | none =>
    have bound := (toU128_none_iff expected).1 result
    have small := actual.isLt
    simp only [runExact, result, Bool.false_eq_true, false_iff]
    omega
  | some value =>
    have equal := (toU128_some_iff expected value).1 result
    simp only [runExact, result, decide_eq_true_eq]
    constructor
    · intro same
      rw [same, BitVec.toNat_setWidth_of_le (show 64 ≤ 128 by decide)] at equal
      exact equal.symm
    · intro same
      apply BitVec.eq_of_toNat_eq
      rw [equal, same, BitVec.toNat_setWidth_of_le (show 64 ≤ 128 by decide)]

/-- Both halves of the 128-bit Option discriminant are defined. None does not
observe its payload. The native success payload starts at output+16. -/
def U128ResultAt (observe : Nat → Nat → Option Nat) (out : Nat) :
    Option (BitVec 128) → Prop
  | none => observe out 8 = some 0 ∧ observe (out + 8) 8 = some 0
  | some value => observe out 8 = some 1 ∧ observe (out + 8) 8 = some 0 ∧
      observe (out + 16) 8 = some (value.setWidth 64).toNat ∧
      observe (out + 24) 8 = some ((value >>> (64 : Nat)).setWidth 64).toNat

/-- Private Result<(), Error> layout. Success defines only its status; failure
keeps the exact original Nat pair and its referenced read-only limbs. -/
def ExactResultAt (observe : Nat → Nat → Option Nat) (out : Nat)
    (expected : NatOperand) (actual : BitVec 64) : Prop :=
  if runExact expected actual then observe (out + 64) 4 = some 0
  else observe out 8 = some 1 ∧ observe (out + 8) 8 = some 0 ∧
    NatArithmetic.operandAt observe (out + 16) expected ∧
    observe (out + 32) 8 = some 0 ∧ observe (out + 40) 8 = some actual.toNat ∧
    observe (out + 48) 8 = some 0 ∧ observe (out + 56) 8 = some 0 ∧
    observe (out + 64) 4 = some 3

end NatNarrow
end SszNative

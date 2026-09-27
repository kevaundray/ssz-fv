import SszNatOperand
import SszArena

set_option autoImplicit false

namespace SszNative.NatArithmetic

inductive Failure where
  | scratchExhausted
  | badRepresentation
  deriving DecidableEq, Repr

/-- Scratch contents include every written limb, even a redundant final zero.
The result may instead borrow a normalized prefix of an original operand. -/
structure Outcome (α : Type) where
  result : Except Failure α
  used : Nat
  allocation : Option Arena.Reservation
  written : List (BitVec 64)
  deriving Repr

def unchanged {α : Type} (used : Nat) (result : Except Failure α) : Outcome α :=
  ⟨result, used, none, []⟩

/-- Called only after a successful reservation; no work is performed on failure. -/
def committed (reservation : Arena.Reservation) (words : List (BitVec 64)) : Outcome NatOperand :=
  ⟨.ok (NatOperand.fromWords (BitVec.ofNat 64 reservation.pointer) words),
    reservation.used, some reservation, words⟩

/-- Exact native Nat::from_u128 branch and allocation order. -/
def fromWide (base capacity used : Nat) (wide : BitVec 128) : Outcome NatOperand :=
  if wide.toNat < 2^64 then
    unchanged used (.ok (.small (wide.setWidth 64)))
  else
    match Arena.reserve base capacity used 2 with
    | none => unchanged used (.error .scratchExhausted)
    | some reservation => committed reservation
        [wide.setWidth 64, (wide >>> 64).setWidth 64]

theorem committed_value (reservation : Arena.Reservation) (words : List (BitVec 64)) :
    (committed reservation words).result.map NatOperand.value = .ok (Limbs.value words) := by
  simp only [committed, Except.map, NatOperand.fromWords_value]

theorem wide_words_value (wide : BitVec 128) :
    Limbs.value [wide.setWidth 64, (wide >>> 64).setWidth 64] = wide.toNat := by
  have physical := wide.isLt
  simp only [Limbs.value, Nat.mul_zero, Nat.add_zero, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have high : wide.toNat / 2^64 < 2^64 := by omega
  rw [Nat.mod_eq_of_lt high]
  exact Nat.mod_add_div wide.toNat (2^64)

theorem fromWide_value (base capacity used : Nat) (wide : BitVec 128)
    (result : NatOperand) (success : (fromWide base capacity used wide).result = .ok result) :
    result.value = wide.toNat := by
  unfold fromWide at success
  split at success
  · rename_i small
    cases success
    simp only [NatOperand.value, NatOperand.words, Limbs.value, Nat.mul_zero,
      Nat.add_zero, BitVec.toNat_setWidth, Nat.mod_eq_of_lt small]
  · split at success
    · cases success
    · rename_i reservation reserved
      cases success
      exact (NatOperand.fromWords_value _ _).trans (wide_words_value wide)

end SszNative.NatArithmetic

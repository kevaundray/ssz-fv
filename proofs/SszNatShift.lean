import SszNatArithmetic
import SszSerializeMeasure

set_option autoImplicit false

/- Shared source model of native/src/nat.rs:316–371, not an ISA theorem.
The logical value is unrestricted. Physical input storage and the u128 shift
argument are separate caller obligations, not logical-number size limits. -/
namespace SszNative.NatShift

open NatArithmetic

def word (operand : NatOperand) (index : Nat) : BitVec 64 :=
  operand.words[index]?.getD 0

/-- Serialize proves the significant-limb scan computes this exact width. -/
def bitLength (operand : NatOperand) : Nat := Serialize.bitLength operand.value

def wordCount (bits : Nat) : Nat := 1 + (bits - 1) / 64

/-- The native right-shift closure; its source indices are physically bounded
at every index actually initialized by shr. -/
def shiftedWord (operand : NatOperand) (bits index : Nat) : BitVec 64 :=
  let source := index + bits / 64
  let shiftBits := bits % 64
  let low := word operand source >>> shiftBits
  if shiftBits ≠ 0 then low ||| (word operand (source + 1) <<< (64 - shiftBits))
  else low

/-- The native left-shift closure, including zero-filled whole low limbs. -/
def leftWord (operand : NatOperand) (bits index : Nat) : BitVec 64 :=
  let whole := bits / 64
  let shiftBits := bits % 64
  if index < whole then 0 else
    let source := index - whole
    let low := word operand source <<< shiftBits
    if shiftBits ≠ 0 ∧ source ≠ 0 then
      low ||| (word operand (source - 1) >>> (64 - shiftBits))
    else low

/-- Unlike arithmetic from_words, shifts return the entire Large buffer. -/
def large (reservation : Arena.Reservation) (words : List (BitVec 64)) : Outcome NatOperand :=
  ⟨.ok (.large (BitVec.ofNat 64 reservation.pointer) words),
    reservation.used, some reservation, words⟩

/-- Reservation occurs before the first limb is computed or initialized. -/
def allocate (base capacity used count : Nat) (generate : Nat → BitVec 64) : Outcome NatOperand :=
  match Arena.reserve base capacity used count with
  | none => unchanged used (.error .scratchExhausted)
  | some reservation => large reservation (List.ofFn (fun i : Fin count => generate i.val))

def shl (operand : NatOperand) (bits base capacity used : Nat) : Outcome NatOperand :=
  let previous := bitLength operand
  if previous = 0 then unchanged used (.ok (.small 0))
  else if bits = 0 then unchanged used (.ok operand.normalized)
  else
    let total := previous + bits
    if total < 2^128 then
      if total ≤ 64 then unchanged used (.ok (.small (word operand 0 <<< bits)))
      else if wordCount total < 2^64 then
        if bits / 64 < 2^64 then
          allocate base capacity used (wordCount total) (leftWord operand bits)
        else unchanged used (.error .scratchExhausted)
      else unchanged used (.error .scratchExhausted)
    else unchanged used (.error .scratchExhausted)

def shr (operand : NatOperand) (bits base capacity used : Nat) : Outcome NatOperand :=
  let previous := bitLength operand
  if previous ≤ bits then unchanged used (.ok (.small 0))
  else if bits = 0 then unchanged used (.ok operand.normalized)
  else
    let total := previous - bits
    if total ≤ 64 then unchanged used (.ok (.small (shiftedWord operand bits 0)))
    else allocate base capacity used (wordCount total) (shiftedWord operand bits)

/-- Zero precedes normalization and every overflow/allocation check. -/
theorem shl_zero (operand : NatOperand) (bits base capacity used : Nat)
    (zero : bitLength operand = 0) :
    shl operand bits base capacity used = unchanged used (.ok (.small 0)) := by
  simp [shl, zero]

theorem shl_zero_bits (operand : NatOperand) (base capacity used : Nat)
    (nonzero : bitLength operand ≠ 0) :
    shl operand 0 base capacity used = unchanged used (.ok operand.normalized) := by
  simp [shl, nonzero]

theorem shr_past_end (operand : NatOperand) (bits base capacity used : Nat)
    (past : bitLength operand ≤ bits) :
    shr operand bits base capacity used = unchanged used (.ok (.small 0)) := by
  simp [shr, past]

theorem shr_zero_bits (operand : NatOperand) (base capacity used : Nat)
    (nonzero : 0 < bitLength operand) :
    shr operand 0 base capacity used = unchanged used (.ok operand.normalized) := by
  simp [shr, show ¬ bitLength operand ≤ 0 by omega]

end SszNative.NatShift

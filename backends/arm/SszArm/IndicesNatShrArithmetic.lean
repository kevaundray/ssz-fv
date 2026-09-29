import SszNatShiftSemantics
import SszIndicesArithmeticSemanticWords

set_option autoImplicit false

namespace SszArm.Indices.NatShr

open SszNative (NatOperand)

/-- NEG W11,W4 followed by the variable 64-bit LSL consumes precisely these
six low bits. The zero-shift path must have branched away first. -/
theorem negated_partial (bits : Nat) (positive : 0 < bits) (small : bits < 64) :
    ((0#32 - BitVec.ofNat 32 bits).toNat % 64) = 64 - bits := by
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- The specialized linked body begins with physical source index zero instead
of computing a whole-limb offset. This is valid only in the supplied range. -/
def loweredWord (operand : NatOperand) (bits position : Nat) : BitVec 64 :=
  (SszNative.NatShift.word operand position >>> (bits % 64)) |||
    (SszNative.NatShift.word operand (position + 1) <<<
      ((0#32 - BitVec.ofNat 32 bits).toNat % 64))

/-- A caller-derived positive shift below 64 makes the literal lowered closure
agree with the unrestricted operational model; no Nat-value cap is needed. -/
theorem loweredWord_correct (operand : NatOperand) (bits position : Nat)
    (positive : 0 < bits) (small : bits < 64) :
    loweredWord operand bits position = SszNative.NatShift.shiftedWord operand bits position := by
  simp only [loweredWord, SszNative.NatShift.shiftedWord,
    Nat.div_eq_of_lt small, Nat.mod_eq_of_lt small, Nat.add_zero,
    negated_partial bits positive small,
    show bits ≠ 0 by omega, ne_eq, not_false_eq_true, ↓reduceIte]

/-- shift_xor/ceil_shift's checked indexing closure agrees with this body when
the physical input slice and the actual caller-derived shift domain hold. -/
theorem loweredWord_indices (operand : NatOperand) (bits position : Nat)
    (physical : operand.words.length < 2^64)
    (positive : 0 < bits) (small : bits < 64) :
    loweredWord operand bits position = SszNative.Indices.shiftedWord operand bits position := by
  rw [SszNative.Indices.shiftedWord_eq_native operand bits position physical]
  exact loweredWord_correct operand bits position positive small

/-- The specialization cannot be extended across the first whole-limb boundary.
This closed discrepancy is independent of addresses and arena capacities. -/
theorem whole_limb_discrepancy (pointer : BitVec 64) :
    loweredWord (.large pointer [5#64, 2#64]) 64 0 = 7#64 ∧
    SszNative.NatShift.shiftedWord (.large pointer [5#64, 2#64]) 64 0 = 2#64 := by
  constructor <;> rfl

end SszArm.Indices.NatShr

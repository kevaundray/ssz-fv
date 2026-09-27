import SszX86.NatDivisionMath
import SszX86.NatDivisionWideMath

namespace SszX86.NatDivision
open SszNative

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem wide_remainder (operand : NatOperand) (divisor lo hi : BitVec 64)
    (count : operand.wordCount ≤ 2) (nonzero : divisor ≠ 0)
    (quotient : Udivti3.value lo hi = operand.value / divisor.toNat) :
    (operand.words[0]?.getD 0) - lo * divisor =
      SszNative.NatDivision.wideRemainder operand divisor := by
  have pair := input_pair operand count
  have q : Udivti3.value lo hi = Udivti3.value
      (operand.words[0]?.getD 0) (operand.words[1]?.getD 0) / divisor.toNat := by
    rw [pair]
    exact quotient
  rw [remainder_from_quotient _ _ divisor lo hi q, pair]
  rw [← SszNative.NatDivision.wideRemainder_toNat operand divisor count nonzero,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Exact unallocated wide-path source outcome selected by the real high
quotient register test. -/
theorem phase_wide_small (operand : NatOperand) (divisor lo : BitVec 64)
    (address capacity used : Nat) (count : operand.wordCount ≤ 2)
    (nonzero : divisor ≠ 0) (notone : divisor ≠ 1)
    (quotient : Udivti3.value lo 0 = operand.value / divisor.toNat) :
    SszNative.NatDivision.run operand divisor address capacity used =
      NatArithmetic.unchanged used (.ok (.small lo,
        (operand.words[0]?.getD 0) - lo * divisor)) := by
  have parts := wide_quotient_parts operand divisor lo 0 count quotient
  have small := parts.2.2.mpr rfl
  rw [SszNative.NatDivision.phase_wide operand divisor address capacity used nonzero notone count]
  simp only [NatArithmetic.fromWide, small, ↓reduceIte, NatArithmetic.unchanged,
    Except.map, parts.1, wide_remainder operand divisor lo 0 count nonzero quotient]

/-- A two-word quotient allocation failure retains the original cursor and
has no allocated or written limbs. -/
theorem phase_wide_failure (operand : NatOperand) (divisor lo hi : BitVec 64)
    (address capacity used : Nat) (count : operand.wordCount ≤ 2)
    (nonzero : divisor ≠ 0) (notone : divisor ≠ 1) (high : hi ≠ 0)
    (quotient : Udivti3.value lo hi = operand.value / divisor.toNat)
    (failure : Arena.reserve address capacity used 2 = none) :
    SszNative.NatDivision.run operand divisor address capacity used =
      NatArithmetic.unchanged used (.error .scratchExhausted) := by
  have parts := wide_quotient_parts operand divisor lo hi count quotient
  have wide : ¬ (SszNative.NatDivision.wideQuotient operand divisor).toNat < 2^64 :=
    fun small => high (parts.2.2.mp small)
  rw [SszNative.NatDivision.phase_wide operand divisor address capacity used nonzero notone count]
  simp only [NatArithmetic.fromWide, wide, ↓reduceIte, failure,
    NatArithmetic.unchanged, Except.map]

/-- Both quotient limbs are written before publication, and the nonzero high
limb makes the exact returned representation Large with length two. -/
theorem phase_wide_reserved (operand : NatOperand) (divisor lo hi : BitVec 64)
    (address capacity used : Nat) (count : operand.wordCount ≤ 2)
    (nonzero : divisor ≠ 0) (notone : divisor ≠ 1) (high : hi ≠ 0)
    (quotient : Udivti3.value lo hi = operand.value / divisor.toNat)
    (allocation : Arena.Reservation)
    (success : Arena.reserve address capacity used 2 = some allocation) :
    SszNative.NatDivision.run operand divisor address capacity used =
      { result := .ok (.large (BitVec.ofNat 64 allocation.pointer) [lo, hi],
          (operand.words[0]?.getD 0) - lo * divisor)
        used := allocation.used
        allocation := some allocation
        written := [lo, hi] } := by
  have parts := wide_quotient_parts operand divisor lo hi count quotient
  have wide : ¬ (SszNative.NatDivision.wideQuotient operand divisor).toNat < 2^64 :=
    fun small => high (parts.2.2.mp small)
  rw [SszNative.NatDivision.phase_wide operand divisor address capacity used nonzero notone count]
  simp only [NatArithmetic.fromWide, wide, ↓reduceIte, success,
    NatArithmetic.committed, Except.map, parts.1, parts.2.1,
    wide_remainder operand divisor lo hi count nonzero quotient]
  have high' : hi ≠ 0#64 := high
  simp [NatOperand.fromWords, Limbs.trim, high']

end SszX86.NatDivision

import SszArm.NatDivisionWide

namespace SszArm.NatDivision

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Link a native quotient pair to the exact shared u128 quotient, without
canonicalizing or replacing the original operand representation. -/
theorem source_wide_pair (operand : SszNative.NatOperand) (divisor low high : BitVec 64)
    (count : operand.wordCount ≤ 2)
    (quotient : Udivti3.join low high = operand.value / divisor.toNat) :
    (SszNative.NatDivision.wideQuotient operand divisor).setWidth 64 = low ∧
      (SszNative.NatDivision.wideQuotient operand divisor >>> 64).setWidth 64 = high := by
  apply join_unique
  rw [join_wide, SszNative.NatDivision.wideQuotient_toNat operand divisor count]
  exact quotient.symm

theorem source_wide_small (operand : SszNative.NatOperand) (divisor low remainder : BitVec 64)
    (base capacity used : Nat) (domain : 2 ≤ divisor.toNat)
    (count : operand.wordCount ≤ 2)
    (quotient : Udivti3.join low 0#64 = operand.value / divisor.toNat)
    (rem : remainder = SszNative.NatDivision.wideRemainder operand divisor) :
    SszNative.NatDivision.run operand divisor base capacity used =
      SszNative.NatArithmetic.unchanged used (.ok (.small low, remainder)) := by
  have nonzero : divisor ≠ 0#64 := by intro h; rw [h] at domain; contradiction
  have notone : divisor ≠ 1#64 := by intro h; rw [h] at domain; contradiction
  have pair := source_wide_pair operand divisor low 0 count quotient
  have small : (SszNative.NatDivision.wideQuotient operand divisor).toNat < 2^64 :=
    (wide_high_zero_iff _).1 pair.2
  rw [SszNative.NatDivision.phase_wide operand divisor base capacity used nonzero notone count]
  simp only [SszNative.NatArithmetic.fromWide, small, ↓reduceIte,
    SszNative.NatArithmetic.unchanged, Except.map, pair.1, rem]

theorem source_wide_exhausted (operand : SszNative.NatOperand) (divisor low high : BitVec 64)
    (base capacity used : Nat) (domain : 2 ≤ divisor.toNat)
    (count : operand.wordCount ≤ 2)
    (quotient : Udivti3.join low high = operand.value / divisor.toNat)
    (wide : high ≠ 0#64)
    (failed : SszNative.Arena.reserve base capacity used 2 = none) :
    SszNative.NatDivision.run operand divisor base capacity used =
      SszNative.NatArithmetic.unchanged used (.error .scratchExhausted) := by
  have nonzero : divisor ≠ 0#64 := by intro h; rw [h] at domain; contradiction
  have notone : divisor ≠ 1#64 := by intro h; rw [h] at domain; contradiction
  have pair := source_wide_pair operand divisor low high count quotient
  have large : ¬ (SszNative.NatDivision.wideQuotient operand divisor).toNat < 2^64 := by
    intro small
    exact wide (pair.2.symm.trans ((wide_high_zero_iff _).2 small))
  rw [SszNative.NatDivision.phase_wide operand divisor base capacity used nonzero notone count]
  simp only [SszNative.NatArithmetic.fromWide, large, ↓reduceIte, failed,
    SszNative.NatArithmetic.unchanged, Except.map]

theorem source_wide_reserved (operand : SszNative.NatOperand)
    (divisor low high remainder : BitVec 64) (base capacity used : Nat)
    (domain : 2 ≤ divisor.toNat) (count : operand.wordCount ≤ 2)
    (quotient : Udivti3.join low high = operand.value / divisor.toNat)
    (wide : high ≠ 0#64)
    (rem : remainder = SszNative.NatDivision.wideRemainder operand divisor)
    (reservation : SszNative.Arena.Reservation)
    (allocated : SszNative.Arena.reserve base capacity used 2 = some reservation) :
    SszNative.NatDivision.run operand divisor base capacity used =
      { result := .ok (SszNative.NatOperand.fromWords (BitVec.ofNat 64 reservation.pointer)
            [low, high], remainder)
        used := reservation.used
        allocation := some reservation
        written := [low, high] } := by
  have nonzero : divisor ≠ 0#64 := by intro h; rw [h] at domain; contradiction
  have notone : divisor ≠ 1#64 := by intro h; rw [h] at domain; contradiction
  have pair := source_wide_pair operand divisor low high count quotient
  have large : ¬ (SszNative.NatDivision.wideQuotient operand divisor).toNat < 2^64 := by
    intro small
    exact wide (pair.2.symm.trans ((wide_high_zero_iff _).2 small))
  rw [SszNative.NatDivision.phase_wide operand divisor base capacity used nonzero notone count]
  simp only [SszNative.NatArithmetic.fromWide, large, ↓reduceIte, allocated,
    SszNative.NatArithmetic.committed, Except.map, pair.1, pair.2, rem]

end SszArm.NatDivision

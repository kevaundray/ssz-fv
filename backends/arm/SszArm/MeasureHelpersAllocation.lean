import SszArm.MeasureAllocationFacts
import SszArm.NatDivisionAllocated

namespace SszArm.Measure.Helpers

open Delimited (Span Protected)
open SszNative (NatOperand)

/-- Physical fresh-buffer protection follows from the actual reserve bounds;
no valid initial cursor or future-state observation is required. -/
theorem fromWide_buffer_owned (writes : List Span) (arena : SszNative.Delimited.ArenaState)
    (wide : BitVec 128) (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (reservation : SszNative.Arena.Reservation)
    (allocated : (SszNative.NatArithmetic.fromWide arena.base arena.capacity arena.used wide).allocation =
      some reservation) :
    NatDivision.OperandOwned writes (.large (BitVec.ofNat 64 reservation.pointer)
      (SszNative.NatArithmetic.fromWide arena.base arena.capacity arena.used wide).written) := by
  have member : SszNative.NatArithmetic.fromWide arena.base arena.capacity arena.used wide ∈
      (SszNative.Serialize.fromWide arena wide).calls := by simp [SszNative.Serialize.fromWide]
  have bounds := (resource_fromWide arena wide).allocations _ member reservation allocated
  have count := fromWide_written_length arena wide reservation allocated
  have pointerBound : reservation.pointer < 2^64 := by omega
  change Protected writes (BitVec.ofNat 64 reservation.pointer).toNat _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pointerBound]
  rcases free with empty | separate
  · omega
  · right
    intro span inWrites
    have apart := separate span inWrites
    have available : arena.used ≤ arena.capacity := by omega
    omega

theorem fromWide_result_owned (writes : List Span) (arena : SszNative.Delimited.ArenaState)
    (wide : BitVec 128) (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (result : NatOperand)
    (success : (SszNative.NatArithmetic.fromWide arena.base arena.capacity arena.used wide).result =
      .ok result) : NatDivision.OperandOwned writes result := by
  by_cases small : wide.toNat < 2^64
  · simp only [SszNative.NatArithmetic.fromWide, small, ↓reduceIte] at success
    cases success
    trivial
  · cases reserved : SszNative.Arena.reserve arena.base arena.capacity arena.used 2 with
    | none =>
      simp only [SszNative.NatArithmetic.fromWide, small, ↓reduceIte, reserved] at success
      cases success
    | some reservation =>
      have buffer := fromWide_buffer_owned writes arena wide storage free reservation (by
        simp [SszNative.NatArithmetic.fromWide, small, reserved, SszNative.NatArithmetic.committed])
      simp only [SszNative.NatArithmetic.fromWide, small, ↓reduceIte, reserved] at success buffer
      cases success
      exact NatDivision.fromWords_owned writes _ _ buffer

theorem fromWide_failure_scratch (arena : SszNative.Delimited.ArenaState) (wide : BitVec 128)
    (reason : SszNative.NatArithmetic.Failure)
    (failure : (SszNative.NatArithmetic.fromWide arena.base arena.capacity arena.used wide).result =
      .error reason) : reason = .scratchExhausted := by
  by_cases small : wide.toNat < 2^64
  · simp [SszNative.NatArithmetic.fromWide, small, SszNative.NatArithmetic.unchanged] at failure
  · cases reserved : SszNative.Arena.reserve arena.base arena.capacity arena.used 2 with
    | none =>
      simpa only [SszNative.NatArithmetic.fromWide, small, ↓reduceIte, reserved,
        SszNative.NatArithmetic.unchanged, Except.error.injEq] using failure.symm
    | some reservation =>
      simp [SszNative.NatArithmetic.fromWide, small, reserved,
        SszNative.NatArithmetic.committed] at failure

end SszArm.Measure.Helpers

import SszArm.MeasureAllocationFacts

namespace SszArm.Measure

/-- A successful word constructor consumes exactly its alignment prefix and
its two written words; the last written byte precedes its committed cursor. -/
theorem fromWide_allocation_end (arena : SszNative.Delimited.ArenaState) (wide : BitVec 128)
    (reservation : SszNative.Arena.Reservation)
    (allocated : (SszNative.NatArithmetic.fromWide arena.base arena.capacity arena.used wide).allocation =
      some reservation) :
    reservation.pointer + 16 = arena.base +
      (SszNative.NatArithmetic.fromWide arena.base arena.capacity arena.used wide).used := by
  by_cases small : wide.toNat < 2^64
  · simp [SszNative.NatArithmetic.fromWide, small, SszNative.NatArithmetic.unchanged] at allocated
  · cases reserved : SszNative.Arena.reserve arena.base arena.capacity arena.used 2 with
    | none =>
      simp [SszNative.NatArithmetic.fromWide, small, reserved,
        SszNative.NatArithmetic.unchanged] at allocated
    | some selected =>
      have same : selected = reservation := by
        simpa only [SszNative.NatArithmetic.fromWide, small, ↓reduceIte, reserved,
          SszNative.NatArithmetic.committed, Option.some.injEq] using allocated
      subst selected
      have exactReservation :=
        ((SszNative.Arena.reserve_eq_some_iff_checks arena.base arena.capacity arena.used 2
          (by decide) reservation).1 reserved).2
      simp only [SszNative.NatArithmetic.fromWide, small, ↓reduceIte, reserved,
        SszNative.NatArithmetic.committed, exactReservation, SszNative.Arena.finish,
        Nat.reduceMul, Nat.add_assoc]

/-- Passing the committed cursor to the second constructor proves non-overlap.
It is valid without a valid-initial-cursor assumption and on later semantic errors. -/
theorem fromWide_allocations_ordered (arena : SszNative.Delimited.ArenaState)
    (firstWide secondWide : BitVec 128) (first second : SszNative.Arena.Reservation)
    (allocatedFirst : (SszNative.NatArithmetic.fromWide arena.base arena.capacity arena.used firstWide).allocation =
      some first)
    (allocatedSecond : (SszNative.NatArithmetic.fromWide arena.base arena.capacity
      (SszNative.NatArithmetic.fromWide arena.base arena.capacity arena.used firstWide).used secondWide).allocation =
        some second) :
    first.pointer + 16 ≤ second.pointer := by
  let nextArena : SszNative.Delimited.ArenaState :=
    { arena with used := (SszNative.NatArithmetic.fromWide arena.base arena.capacity arena.used firstWide).used }
  have later := (resource_fromWide nextArena secondWide).allocations
    (SszNative.NatArithmetic.fromWide nextArena.base nextArena.capacity nextArena.used secondWide)
    (by simp only [SszNative.Serialize.fromWide, List.mem_singleton]) second allocatedSecond
  rw [fromWide_allocation_end arena firstWide first allocatedFirst]
  exact later.1

end SszArm.Measure

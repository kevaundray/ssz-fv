import SszArm.MeasureResources

namespace SszArm.Measure

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value Outcome)

/-- Measurement reserves words only through the accepted two-limb constructor. -/
def CallsTwo {α : Type} (measured : Outcome α) : Prop :=
  ∀ call ∈ measured.calls, ∀ reservation, call.allocation = some reservation →
    call.written.length = 2

theorem callsTwo_unchanged {α : Type} (used : Nat)
    (result : Except SszNative.Serialize.Error α) :
    CallsTwo (SszNative.Serialize.unchanged used result) := by
  intro call member
  simp [SszNative.Serialize.unchanged] at member

theorem fromWide_written_length (arena : SszNative.Delimited.ArenaState) (wide : BitVec 128)
    (reservation : SszNative.Arena.Reservation)
    (allocated : (SszNative.NatArithmetic.fromWide arena.base arena.capacity arena.used wide).allocation =
      some reservation) :
    (SszNative.NatArithmetic.fromWide arena.base arena.capacity arena.used wide).written.length = 2 := by
  by_cases small : wide.toNat < 2^64
  · simp [SszNative.NatArithmetic.fromWide, small, SszNative.NatArithmetic.unchanged] at allocated
  · cases reserved : SszNative.Arena.reserve arena.base arena.capacity arena.used 2 with
    | none =>
      simp [SszNative.NatArithmetic.fromWide, small, reserved,
        SszNative.NatArithmetic.unchanged] at allocated
    | some selected =>
      simp [SszNative.NatArithmetic.fromWide, small, reserved,
        SszNative.NatArithmetic.committed]

theorem callsTwo_fromWide (arena : SszNative.Delimited.ArenaState) (wide : BitVec 128) :
    CallsTwo (SszNative.Serialize.fromWide arena wide) := by
  intro call member reservation allocated
  simp only [SszNative.Serialize.fromWide, List.mem_singleton] at member
  subst call
  exact fromWide_written_length arena wide reservation allocated

theorem callsTwo_bind {α β : Type} (first : Outcome α) (next : α → Nat → Outcome β)
    (earlier : CallsTwo first)
    (later : ∀ actual, first.result = .ok actual → CallsTwo (next actual first.used)) :
    CallsTwo (SszNative.Serialize.bind first next) := by
  intro call member reservation allocated
  cases checked : first.result with
  | error reason =>
    exact earlier call (by simpa only [SszNative.Serialize.bind, checked] using member)
      reservation allocated
  | ok actual =>
    simp only [SszNative.Serialize.bind, checked, List.mem_append] at member
    rcases member with before | after
    · exact earlier call before reservation allocated
    · exact later actual checked call after reservation allocated

theorem callsTwo_bounded (cap : Option NatOperand) (actual : NatOperand) (used : Nat) :
    CallsTwo (SszNative.Serialize.bounded cap actual used) := by
  cases cap with
  | none => exact callsTwo_unchanged used _
  | some operand =>
    by_cases fits : actual.value ≤ operand.value
    · simpa only [SszNative.Serialize.bounded, fits, ↓reduceIte] using
        callsTwo_unchanged used (.ok ())
    · simpa only [SszNative.Serialize.bounded, fits, ↓reduceIte] using
        callsTwo_unchanged used (.error (.limit operand actual))

theorem callsTwo_measureList (arena : SszNative.Delimited.ArenaState)
    (cap : Option NatOperand) (bits : SszNative.Serialize.Packed) :
    CallsTwo (SszNative.Serialize.measureList cap bits arena) := by
  unfold SszNative.Serialize.measureList
  apply callsTwo_bind _ _ (callsTwo_fromWide arena bits.count)
  intro actual counted
  apply callsTwo_bind _ _ (callsTwo_bounded cap actual _)
  intro ignored checked
  exact callsTwo_fromWide _ _

theorem callsTwo_measure (arena : SszNative.Delimited.ArenaState) (desc : Desc) (value : Value) :
    CallsTwo (SszNative.Serialize.measure desc value arena) := by
  cases desc <;> cases value <;> simp only [SszNative.Serialize.measure]
  all_goals first
    | exact callsTwo_unchanged _ _
    | exact callsTwo_measureList arena _ _
    | (split <;> exact callsTwo_unchanged _ _)
    | (apply callsTwo_bind _ _ (callsTwo_bounded _ _ _)
       intro actual checked
       exact callsTwo_unchanged _ _)
    | (split
       · exact callsTwo_unchanged _ _
       · apply callsTwo_bind _ _ (callsTwo_fromWide arena _)
         intro actual checked
         exact callsTwo_unchanged _ _)

end SszArm.Measure

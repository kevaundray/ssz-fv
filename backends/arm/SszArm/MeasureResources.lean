import SszArm.MeasureContract

namespace SszArm.Measure

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value Outcome)

/-- Every committed limb write lies in the original free suffix. This is derived
from the actual constructor guards, including for initially invalid cursors. -/
structure ResourceBounds {α : Type} (arena : SszNative.Delimited.ArenaState)
    (measured : Outcome α) : Prop where
  monotone : arena.used ≤ measured.used
  allocations : ∀ call ∈ measured.calls, ∀ reservation, call.allocation = some reservation →
    arena.base + arena.used ≤ reservation.pointer ∧
    reservation.pointer + 8 * call.written.length ≤ arena.base + arena.capacity

theorem resource_unchanged {α : Type} (arena : SszNative.Delimited.ArenaState)
    (result : Except SszNative.Serialize.Error α) :
    ResourceBounds arena (SszNative.Serialize.unchanged arena.used result) := by
  refine ⟨Nat.le_refl _, ?_⟩
  intro call member
  simp [SszNative.Serialize.unchanged] at member

theorem resource_fromWide (arena : SszNative.Delimited.ArenaState) (wide : BitVec 128) :
    ResourceBounds arena (SszNative.Serialize.fromWide arena wide) := by
  by_cases small : wide.toNat < 2^64
  · constructor
    · simp [SszNative.Serialize.fromWide, SszNative.NatArithmetic.fromWide, small,
        SszNative.NatArithmetic.unchanged]
    · intro call member reservation allocated
      simp only [SszNative.Serialize.fromWide, SszNative.NatArithmetic.fromWide,
        small, ↓reduceIte, List.mem_singleton] at member
      subst call
      simp [SszNative.NatArithmetic.unchanged] at allocated
  · cases reserved : SszNative.Arena.reserve arena.base arena.capacity arena.used 2 with
    | none =>
      constructor
      · simp [SszNative.Serialize.fromWide, SszNative.NatArithmetic.fromWide, small,
          reserved, SszNative.NatArithmetic.unchanged]
      · intro call member reservation allocated
        simp only [SszNative.Serialize.fromWide, SszNative.NatArithmetic.fromWide,
          small, ↓reduceIte, reserved, List.mem_singleton] at member
        subst call
        simp [SszNative.NatArithmetic.unchanged] at allocated
    | some reservation =>
      obtain ⟨checks, exactReservation⟩ :=
        (SszNative.Arena.reserve_eq_some_iff_checks arena.base arena.capacity arena.used 2
          (by decide) reservation).1 reserved
      have start := SszNative.Arena.used_le_start arena.base arena.used
      have capacity := checks.2.2.2.2.2
      constructor
      · simp only [SszNative.Serialize.fromWide, SszNative.NatArithmetic.fromWide,
          small, ↓reduceIte, reserved, SszNative.NatArithmetic.committed, exactReservation]
        unfold SszNative.Arena.finish
        omega
      · intro call member selected allocated
        simp only [SszNative.Serialize.fromWide, SszNative.NatArithmetic.fromWide,
          small, ↓reduceIte, reserved, List.mem_singleton] at member
        subst call
        have same : reservation = selected := Option.some.inj allocated
        subst selected
        simp only [SszNative.NatArithmetic.committed, List.length_cons, List.length_nil,
          exactReservation]
        unfold SszNative.Arena.finish at capacity
        constructor <;> omega

theorem resource_bind {α β : Type} (arena : SszNative.Delimited.ArenaState)
    (first : Outcome α) (next : α → Nat → Outcome β)
    (firstBounds : ResourceBounds arena first)
    (nextBounds : ∀ actual, first.result = .ok actual →
      ResourceBounds { arena with used := first.used } (next actual first.used)) :
    ResourceBounds arena (SszNative.Serialize.bind first next) := by
  cases checked : first.result with
  | error reason =>
    constructor
    · simpa only [SszNative.Serialize.bind, checked] using firstBounds.monotone
    · intro call member reservation allocated
      exact firstBounds.allocations call
        (by simpa only [SszNative.Serialize.bind, checked] using member) reservation allocated
  | ok actual =>
    have second := nextBounds actual checked
    constructor
    · simpa only [SszNative.Serialize.bind, checked] using
        Nat.le_trans firstBounds.monotone second.monotone
    · intro call member reservation allocated
      simp only [SszNative.Serialize.bind, checked, List.mem_append] at member
      rcases member with earlier | later
      · exact firstBounds.allocations call earlier reservation allocated
      · obtain ⟨low, high⟩ := second.allocations call later reservation allocated
        exact ⟨by have monotone := firstBounds.monotone; dsimp at low; omega, high⟩

theorem resource_bounded (arena : SszNative.Delimited.ArenaState)
    (cap : Option NatOperand) (actual : NatOperand) :
    ResourceBounds arena (SszNative.Serialize.bounded cap actual arena.used) := by
  cases cap with
  | none => exact resource_unchanged arena _
  | some operand =>
    by_cases fits : actual.value ≤ operand.value
    · simpa only [SszNative.Serialize.bounded, fits, ↓reduceIte] using
        resource_unchanged arena (.ok ())
    · simpa only [SszNative.Serialize.bounded, fits, ↓reduceIte] using
        resource_unchanged arena (.error (.limit operand actual))

theorem resource_measureList (arena : SszNative.Delimited.ArenaState)
    (cap : Option NatOperand) (bits : SszNative.Serialize.Packed) :
    ResourceBounds arena (SszNative.Serialize.measureList cap bits arena) := by
  unfold SszNative.Serialize.measureList
  apply resource_bind arena _ _ (resource_fromWide arena bits.count)
  intro actual counted
  apply resource_bind _ _ _ (resource_bounded _ cap actual)
  intro ignored checked
  exact resource_fromWide _ _

theorem resource_measure (arena : SszNative.Delimited.ArenaState) (desc : Desc) (value : Value) :
    ResourceBounds arena (SszNative.Serialize.measure desc value arena) := by
  cases desc <;> cases value <;> simp only [SszNative.Serialize.measure]
  all_goals first
    | exact resource_unchanged arena _
    | exact resource_measureList arena _ _
    | (split <;> exact resource_unchanged arena _)
    | (apply resource_bind arena _ _ (resource_bounded arena _ _)
       intro actual checked
       exact resource_unchanged _ _)
    | (split
       · exact resource_unchanged arena _
       · apply resource_bind arena _ _ (resource_fromWide arena _)
         intro actual checked
         exact resource_unchanged _ _)

end SszArm.Measure

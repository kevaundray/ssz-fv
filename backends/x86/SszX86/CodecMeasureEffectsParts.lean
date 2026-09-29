import SszX86.CodecMeasureEffectsLoop

namespace SszX86.CodecMeasure.Geometry
open SszNative
open SszNative.CodecMeasure

/-- The actual outer reservation covers just the paired prefix. Zero counts
impose no dangling-pointer condition, and final arity or arithmetic failures do
not discard the initialized bytes from the preceding loop. -/
theorem measureParts_within (parts : Parts) (values : List Codec.Value) (visit : Visit values)
    (arena : Delimited.ArenaState) (retain : Bool)
    (bounded : arena.base + arena.capacity ≤ 2 ^ 64)
    (safeVisit : ∀ value member desc site keep,
      CursorSafe site (visit value member desc site keep).used)
    (visitWithin : ∀ value member desc site keep,
      site.base + site.capacity ≤ 2 ^ 64 →
      Within (site.base + site.used) (site.base + site.capacity)
        (visit value member desc site keep).effects) :
    Within (arena.base + arena.used) (arena.base + arena.capacity)
      (measureParts parts values visit arena retain).effects := by
  have run (allocation : Option Arena.Reservation) (used : Nat)
      (monotone : arena.used ≤ used)
      (slots : Slots (arena.base + arena.used) (arena.base + arena.capacity)
        allocation 0 (parts.paired values)) :
      Within (arena.base + arena.used) (arena.base + arena.capacity)
        (bind (measureLoop parts values visit (retain && !parts.allFixed) allocation 0 initial
          { arena with used := used })
          (fun totals used => finishParts parts values totals allocation
            { arena with used := used })).effects := by
    apply bind_within _ _ _ _
      (measureLoop_within parts values visit (retain && !parts.allFixed) allocation 0 initial
        { arena with used := used } (arena.base + arena.used)
        (Nat.add_le_add_left monotone arena.base) bounded slots safeVisit visitWithin)
    intro totals _measured
    apply (finishParts_within parts values totals allocation _ bounded).weaken
      ?_ (Nat.le_refl _)
    exact Nat.add_le_add_left
      (monotone.trans
        (measureLoop_cursorSafe parts values visit (retain && !parts.allFixed) allocation 0
          initial { arena with used := used } safeVisit).1) arena.base
  unfold measureParts
  dsimp only
  split
  · apply bind_within _ _ _ _ (reservePlans_within _ _ _ _)
    intro allocation result
    exact run (some allocation) _ (reservePlans_cursorSafe _ arena).1
      (reserved_slots (parts.paired values) arena allocation bounded
        (reservePlans_allocation (parts.paired values) arena allocation result))
  · apply run none arena.used (Nat.le_refl _)
    intro reservation impossible
    cases impossible

/-- The composite cursor bound is independent of the stronger `Arena.Valid`
predicate and holds for errors as well as successful plans. -/
theorem measureParts_capacity (parts : Parts) (values : List Codec.Value) (visit : Visit values)
    (arena : Delimited.ArenaState) (retain : Bool) (initial : arena.used ≤ arena.capacity)
    (visitCapacity : ∀ value member desc site keep, site.used ≤ site.capacity →
      (visit value member desc site keep).used ≤ site.capacity) :
    (measureParts parts values visit arena retain).used ≤ arena.capacity := by
  unfold measureParts
  dsimp only
  split
  · apply bind_capacity _ _ _ (reservePlans_capacity _ arena initial)
    intro allocation used bound
    apply bind_capacity _ _ _ (measureLoop_capacity _ _ _ _ _ _ _ _ bound visitCapacity)
    intro totals used bound
    exact finishParts_capacity _ _ _ _ _ bound
  · apply bind_capacity _ _ _ (measureLoop_capacity _ _ _ _ _ _ _ _ initial visitCapacity)
    intro totals used bound
    exact finishParts_capacity _ _ _ _ _ bound

end SszX86.CodecMeasure.Geometry

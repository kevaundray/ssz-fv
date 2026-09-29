import SszX86.CodecMeasureEffectsGeometry
import SszX86.CodecMeasureEffectsCombinators

namespace SszX86.CodecMeasure.Geometry
open SszNative
open SszNative.CodecMeasure

/-- Every initialized loop byte lies above the original lower bound. The slot
interval shrinks with the actual paired prefix, not with either arity alone;
failed visits and additions retain the already bounded effects through `bind`. -/
theorem measureLoop_within (parts : Parts) (values : List Codec.Value) (visit : Visit values)
    (keep : Bool) (allocation : Option Arena.Reservation) (index : Nat)
    (totals : Partial) (arena : Delimited.ArenaState) (low : Nat)
    (lower : low ≤ arena.base + arena.used)
    (bounded : arena.base + arena.capacity ≤ 2 ^ 64)
    (slots : Slots low (arena.base + arena.capacity) allocation index (parts.paired values))
    (safeVisit : ∀ value member desc site retain,
      CursorSafe site (visit value member desc site retain).used)
    (visitWithin : ∀ value member desc site retain,
      site.base + site.capacity ≤ 2 ^ 64 →
      Within (site.base + site.used) (site.base + site.capacity)
        (visit value member desc site retain).effects) :
    Within low (arena.base + arena.capacity)
      (measureLoop parts values visit keep allocation index totals arena).effects := by
  induction values generalizing parts index totals arena with
  | nil =>
    rw [measureLoop]
    exact unchanged_within _ _ _ _
  | cons value rest ih =>
    cases parts with
    | repeated element =>
      have paired : Parts.paired (.repeated element) (value :: rest) =
          Parts.paired (.repeated element) rest + 1 := rfl
      rw [paired] at slots
      have current : Slots low (arena.base + arena.capacity) allocation index 1 := by
        intro reservation allocated i first last
        exact slots reservation allocated i first (by omega)
      have remaining := slots.tail
      let visited := visit value (by simp) element arena keep
      let childArena : Delimited.ArenaState := { arena with used := visited.used }
      have childLower : low ≤ childArena.base + childArena.used :=
        lower.trans (Nat.add_le_add_left (safeVisit value _ element arena keep).1 arena.base)
      simp only [measureLoop]
      apply bind_within _ _ _ _
        ((visitWithin value _ element arena keep bounded).weaken lower (Nat.le_refl _))
      intro child _visited
      let accumulated := accumulate (FixedSize.isFixed element) child totals childArena
      have nextLower : low ≤ arena.base + accumulated.used :=
        childLower.trans
          (Nat.add_le_add_left (accumulate_cursorSafe _ _ _ childArena).1 arena.base)
      apply bind_within _ _ _ _
        ((accumulate_within _ _ _ childArena bounded).weaken childLower (Nat.le_refl _))
      intro next _accumulated
      apply bind_within _ _ _ _ (writePlan_within _ _ index _ allocation child bounded current)
      intro checked _written
      simp only [writePlan_used]
      apply ih
      · exact nextLower
      · exact bounded
      · exact remaining
      · intro actual member desc site retain
        exact safeVisit actual (List.mem_cons_of_mem _ member) desc site retain
      · intro actual member desc site retain siteBounded
        exact visitWithin actual (List.mem_cons_of_mem _ member) desc site retain siteBounded
    | fields fields =>
      cases fields with
      | nil =>
        rw [measureLoop]
        exact unchanged_within _ _ _ _
      | cons field fields =>
        rcases field with ⟨name, desc⟩
        have paired : Parts.paired (.fields ((name, desc) :: fields)) (value :: rest) =
            Parts.paired (.fields fields) rest + 1 := by
          simp only [Parts.paired, List.length_cons]
          omega
        rw [paired] at slots
        have current : Slots low (arena.base + arena.capacity) allocation index 1 := by
          intro reservation allocated i first last
          exact slots reservation allocated i first (by omega)
        have remaining := slots.tail
        let visited := visit value (by simp) desc arena keep
        let childArena : Delimited.ArenaState := { arena with used := visited.used }
        have childLower : low ≤ childArena.base + childArena.used :=
          lower.trans (Nat.add_le_add_left (safeVisit value _ desc arena keep).1 arena.base)
        simp only [measureLoop]
        apply bind_within _ _ _ _
          ((visitWithin value _ desc arena keep bounded).weaken lower (Nat.le_refl _))
        intro child _visited
        let accumulated := accumulate (FixedSize.isFixed desc) child totals childArena
        have nextLower : low ≤ arena.base + accumulated.used :=
          childLower.trans
            (Nat.add_le_add_left (accumulate_cursorSafe _ _ _ childArena).1 arena.base)
        apply bind_within _ _ _ _
          ((accumulate_within _ _ _ childArena bounded).weaken childLower (Nat.le_refl _))
        intro next _accumulated
        apply bind_within _ _ _ _ (writePlan_within _ _ index _ allocation child bounded current)
        intro checked _written
        simp only [writePlan_used]
        apply ih
        · exact nextLower
        · exact bounded
        · exact remaining
        · intro actual member desc site retain
          exact safeVisit actual (List.mem_cons_of_mem _ member) desc site retain
        · intro actual member desc site retain siteBounded
          exact visitWithin actual (List.mem_cons_of_mem _ member) desc site retain siteBounded

/-- Capacity preservation needs only the incoming cursor bound, including for
null or empty arenas and arbitrary logical metadata. -/
theorem measureLoop_capacity (parts : Parts) (values : List Codec.Value) (visit : Visit values)
    (keep : Bool) (allocation : Option Arena.Reservation) (index : Nat)
    (totals : Partial) (arena : Delimited.ArenaState) (initial : arena.used ≤ arena.capacity)
    (visitCapacity : ∀ value member desc site retain, site.used ≤ site.capacity →
      (visit value member desc site retain).used ≤ site.capacity) :
    (measureLoop parts values visit keep allocation index totals arena).used ≤ arena.capacity := by
  induction values generalizing parts index totals arena with
  | nil =>
    rw [measureLoop]
    exact initial
  | cons value rest ih =>
    cases parts with
    | repeated element =>
      simp only [measureLoop]
      apply bind_capacity _ _ _ (visitCapacity value _ element arena keep initial)
      intro child used bound
      apply bind_capacity _ _ _ (accumulate_capacity _ _ _ { arena with used := used } bound)
      intro next used bound
      apply bind_capacity _ _ _ (by rw [writePlan_used]; exact bound)
      intro checked used bound
      apply ih
      · exact bound
      · intro actual member desc site retain siteBound
        exact visitCapacity actual (List.mem_cons_of_mem _ member) desc site retain siteBound
    | fields fields =>
      cases fields with
      | nil =>
        rw [measureLoop]
        exact initial
      | cons field fields =>
        rcases field with ⟨name, desc⟩
        simp only [measureLoop]
        apply bind_capacity _ _ _ (visitCapacity value _ desc arena keep initial)
        intro child used bound
        apply bind_capacity _ _ _ (accumulate_capacity _ _ _ { arena with used := used } bound)
        intro next used bound
        apply bind_capacity _ _ _ (by rw [writePlan_used]; exact bound)
        intro checked used bound
        apply ih
        · exact bound
        · intro actual member desc site retain siteBound
          exact visitCapacity actual (List.mem_cons_of_mem _ member) desc site retain siteBound

end SszX86.CodecMeasure.Geometry

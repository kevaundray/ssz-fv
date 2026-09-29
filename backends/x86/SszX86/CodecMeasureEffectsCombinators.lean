import SszX86.CodecMeasureEffectsPrimitives
import SszCodecMeasureResources

namespace SszX86.CodecMeasure.Geometry
open SszNative
open SszNative.CodecMeasure

theorem accumulate_within (inline : Bool) (child : Plan) (totals : Partial)
    (arena : Delimited.ArenaState) (bounded : arena.base + arena.capacity ≤ 2 ^ 64) :
    Within (arena.base + arena.used) (arena.base + arena.capacity)
      (accumulate inline child totals arena).effects := by
  unfold accumulate
  apply bind_within _ _ _ _ (add_within _ _ arena bounded)
  intro leading result
  split
  · exact unchanged_within _ _ _ _
  · apply bind_within _ _ _ _
      ((add_within _ _ _ bounded).weaken
        (Nat.add_le_add_left (add_cursorSafe _ _ arena).1 arena.base) (Nat.le_refl _))
    intro bodies result
    exact unchanged_within _ _ _ _

theorem finishParts_within (parts : Parts) (values : List Codec.Value) (totals : Partial)
    (allocation : Option Arena.Reservation) (arena : Delimited.ArenaState)
    (bounded : arena.base + arena.capacity ≤ 2 ^ 64) :
    Within (arena.base + arena.used) (arena.base + arena.capacity)
      (finishParts parts values totals allocation arena).effects := by
  unfold finishParts
  split
  · apply bind_within _ _ _ _ (add_within _ _ arena bounded)
    intro size result
    apply bind_within _ _ _ _ (compositeSize_within _ _ _ _)
    intro checked result
    apply bind_within _ _ _ _ (hostSize_within _ _ _ _)
    intro leading result
    exact unchanged_within _ _ _ _
  · exact unchanged_within _ _ _ _

theorem unionPlan_within (child : Plan) (arena : Delimited.ArenaState) (retain : Bool)
    (bounded : arena.base + arena.capacity ≤ 2 ^ 64) :
    Within (arena.base + arena.used) (arena.base + arena.capacity)
      (unionPlan child arena retain).effects := by
  unfold unionPlan
  apply bind_within _ _ _ _ (add_within _ _ arena bounded)
  intro size result
  split
  · apply bind_within _ _ _ _ (reservePlans_within _ _ _ _)
    intro allocation result
    have reserved := reservePlans_allocation 1
      { arena with used := (add child.size (.small 1) arena).used } allocation result
    have slots := reserved_slots 1
      { arena with used := (add child.size (.small 1) arena).used } allocation bounded reserved
    apply bind_within _ _ _ _
      ((writePlan_within _ _ 0 _ (some allocation) child bounded slots).weaken
        (Nat.add_le_add_left (add_cursorSafe _ _ arena).1 arena.base) (Nat.le_refl _))
    intro checked result
    exact unchanged_within _ _ _ _
  · exact unchanged_within _ _ _ _

theorem bind_capacity {α β : Type} (capacity : Nat) (first : Outcome α)
    (next : α → Nat → Outcome β) (before : first.used ≤ capacity)
    (after : ∀ value used, used ≤ capacity → (next value used).used ≤ capacity) :
    (bind first next).used ≤ capacity := by
  cases result : first.result with
  | error reason => simpa only [bind, result] using before
  | ok value => simpa only [bind, result] using after value first.used before

theorem add_capacity (left right : NatOperand) (arena : Delimited.ArenaState)
    (bounded : arena.used ≤ arena.capacity) : (add left right arena).used ≤ arena.capacity :=
  (CodecMeasureFixed.add_cursor_bounds left right arena.base arena.capacity arena.used bounded).2

theorem reservePlans_capacity (count : Nat) (arena : Delimited.ArenaState)
    (bounded : arena.used ≤ arena.capacity) : (reservePlans count arena).used ≤ arena.capacity := by
  unfold reservePlans
  split
  · exact bounded
  · rename_i reservation reserved
    by_cases zero : 5 * count = 0
    · rw [zero] at reserved
      rw [(Arena.reserve_zero_properties _ _ _ reservation reserved).2.2.2]
      exact bounded
    · obtain ⟨checks, shape⟩ :=
        (Arena.reserve_eq_some_iff_checks arena.base arena.capacity arena.used
          (5 * count) (by omega) reservation).1 reserved
      rw [shape]
      exact checks.2.2.2.2.2

theorem accumulate_capacity (inline : Bool) (child : Plan) (totals : Partial)
    (arena : Delimited.ArenaState) (bounded : arena.used ≤ arena.capacity) :
    (accumulate inline child totals arena).used ≤ arena.capacity := by
  unfold accumulate
  apply bind_capacity _ _ _ (add_capacity _ _ arena bounded)
  intro leading used bound
  split
  · exact bound
  · apply bind_capacity _ _ _ (add_capacity _ _ { arena with used := used } bound)
    intro bodies used bound
    exact bound

theorem finishParts_capacity (parts : Parts) (values : List Codec.Value) (totals : Partial)
    (allocation : Option Arena.Reservation) (arena : Delimited.ArenaState)
    (bounded : arena.used ≤ arena.capacity) :
    (finishParts parts values totals allocation arena).used ≤ arena.capacity := by
  unfold finishParts
  split
  · apply bind_capacity _ _ _ (add_capacity _ _ arena bounded)
    intro size used bound
    apply bind_capacity _ _ _ (by rw [(compositeSize_resources size used).1]; exact bound)
    intro checked used bound
    apply bind_capacity _ _ _ (by rw [(hostSize_resources totals.leading used).1]; exact bound)
    intro leading used bound
    exact bound
  · exact bounded

theorem unionPlan_capacity (child : Plan) (arena : Delimited.ArenaState) (retain : Bool)
    (bounded : arena.used ≤ arena.capacity) :
    (unionPlan child arena retain).used ≤ arena.capacity := by
  unfold unionPlan
  apply bind_capacity _ _ _ (add_capacity _ _ arena bounded)
  intro size used bound
  split
  · apply bind_capacity _ _ _ (reservePlans_capacity 1 { arena with used := used } bound)
    intro allocation used bound
    apply bind_capacity _ _ _ (by rw [writePlan_used]; exact bound)
    intro checked used bound
    exact bound
  · exact bound

end SszX86.CodecMeasure.Geometry

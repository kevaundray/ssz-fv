import SszX86.CodecMeasureEffectsParts
import SszX86.CodecMeasurePrimitiveCapacity

namespace SszX86.CodecMeasure.Geometry
open SszNative
open SszNative.Codec (Desc Value)
open SszNative.CodecMeasure

private theorem bind_arena_within {α β : Type} (arena : Delimited.ArenaState)
    (first : Outcome α) (next : α → Nat → Outcome β)
    (monotone : arena.used ≤ first.used)
    (before : Within (arena.base + arena.used) (arena.base + arena.capacity) first.effects)
    (after : ∀ value, first.result = .ok value →
      Within (arena.base + first.used) (arena.base + arena.capacity) (next value first.used).effects) :
    Within (arena.base + arena.used) (arena.base + arena.capacity) (bind first next).effects := by
  apply bind_within _ _ _ _ before
  intro value success
  exact (after value success).weaken (Nat.add_le_add_left monotone _) (Nat.le_refl _)

theorem measureStep_within (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (retain : Bool) (visit : Visit value.children)
    (bounded : arena.base + arena.capacity ≤ 2 ^ 64)
    (safeVisit : ∀ child member desc site keep,
      CursorSafe site (visit child member desc site keep).used)
    (visitWithin : ∀ child member desc site keep, site.base + site.capacity ≤ 2 ^ 64 →
      Within (site.base + site.used) (site.base + site.capacity) (visit child member desc site keep).effects) :
    Within (arena.base + arena.used) (arena.base + arena.capacity)
      (measureStep desc value arena retain visit).effects := by
  cases desc <;> cases value <;> simp only [measureStep]
  all_goals first
    | exact primitive_within _ _ arena bounded
    | exact unchanged_within _ _ _ _
    | exact measureParts_within _ _ _ _ _ bounded safeVisit visitWithin
    | (apply bind_arena_within arena _ _
         (by rw [(exactCount_resources _ _ _).1]) (exactCount_within _ _ _ _ _)
       intro _checked _
       exact measureParts_within _ _ _ _ _ bounded safeVisit visitWithin)
    | (apply bind_arena_within arena _ _
         (by rw [(bounded_resources _ _ _).1]) (bounded_within _ _ _ _ _)
       intro _checked _
       exact measureParts_within _ _ _ _ _ bounded safeVisit visitWithin)
    | (apply bind_arena_within arena _ _ (Nat.le_refl _) (unchanged_within _ _ _ _)
       intro chosen _
       apply bind_arena_within _ _ _ (safeVisit _ _ chosen _ retain).1
         (visitWithin _ _ chosen _ retain bounded)
       intro child _
       exact unionPlan_within child _ retain bounded)

/-- Every initialized byte of an actual recursive measurement belongs to the
original arena's free suffix, including effects retained by later failures. -/
theorem measure_within (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (retain : Bool) (bounded : arena.base + arena.capacity ≤ 2 ^ 64) :
    Within (arena.base + arena.used) (arena.base + arena.capacity)
      (measure desc value arena retain).effects := by
  rw [measure]
  apply measureStep_within desc value arena retain _ bounded
  · intro child _member childDesc site keep
    exact measure_cursorSafe childDesc child site keep
  · intro child _member childDesc site keep siteBound
    exact measure_within childDesc child site keep siteBound
termination_by value.nesting
decreasing_by exact Value.child_nesting_lt _ _ (by assumption)

private theorem bind_capacity_at_result {α β : Type} (capacity : Nat) (first : Outcome α)
    (next : α → Nat → Outcome β) (before : first.used ≤ capacity)
    (after : ∀ value, first.result = .ok value → (next value first.used).used ≤ capacity) :
    (bind first next).used ≤ capacity := by
  cases result : first.result with
  | error reason => simpa only [bind, result] using before
  | ok value => simpa only [bind, result] using after value result

theorem measureStep_capacity (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (retain : Bool) (visit : Visit value.children) (initial : arena.used ≤ arena.capacity)
    (visitCapacity : ∀ child member desc site keep, site.used ≤ site.capacity →
      (visit child member desc site keep).used ≤ site.capacity) :
    (measureStep desc value arena retain visit).used ≤ arena.capacity := by
  cases desc <;> cases value <;> simp only [measureStep]
  all_goals first
    | exact primitive_capacity _ _ arena initial
    | exact initial
    | exact measureParts_capacity _ _ _ _ _ initial visitCapacity
    | (apply bind_capacity_at_result _ _ _ (by rw [(exactCount_resources _ _ _).1]; exact initial)
       intro _checked _
       apply measureParts_capacity _ _ _ _ _ _ visitCapacity
       rw [(exactCount_resources _ _ _).1]
       exact initial)
    | (apply bind_capacity_at_result _ _ _ (by rw [(bounded_resources _ _ _).1]; exact initial)
       intro _checked _
       apply measureParts_capacity _ _ _ _ _ _ visitCapacity
       rw [(bounded_resources _ _ _).1]
       exact initial)
    | (apply bind_capacity_at_result _ _ _ initial
       intro chosen _
       apply bind_capacity_at_result _ _ _ (visitCapacity _ _ chosen _ retain initial)
       intro child _
       exact unionPlan_capacity child _ retain (visitCapacity _ _ chosen _ retain initial))

/-- Capacity safety needs only the actual initial cursor bound, not the stronger
`Arena.Valid` conditions used by some legacy convenience theorems. -/
theorem measure_capacity (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (retain : Bool) (initial : arena.used ≤ arena.capacity) :
    (measure desc value arena retain).used ≤ arena.capacity := by
  rw [measure]
  apply measureStep_capacity desc value arena retain _ initial
  intro child _member childDesc site keep siteBound
  exact measure_capacity childDesc child site keep siteBound
termination_by value.nesting
decreasing_by exact Value.child_nesting_lt _ _ (by assumption)

theorem effects_in_free (desc : Desc) (value : Value) (address capacity used : BitVec 64)
    (retain : Bool) (bounded : address.toNat + capacity.toNat ≤ 2 ^ 64)
    (a : BitVec 64)
    (writes : EffectsWrite
      (measure desc value (Measure.arenaState address capacity used) retain).effects a) :
    Codec.InSpan a (address + used) (capacity.toNat - used.toNat) := by
  obtain ⟨lower, upper⟩ := measure_within desc value (Measure.arenaState address capacity used)
    retain bounded a writes
  change address.toNat + used.toNat ≤ a.toNat at lower
  change a.toNat < address.toNat + capacity.toNat at upper
  refine ⟨a.toNat - (address.toNat + used.toNat), by omega, ?_⟩
  bv_omega

end SszX86.CodecMeasure.Geometry

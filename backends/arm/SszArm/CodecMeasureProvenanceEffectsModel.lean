import SszArm.CodecMeasureProvenance
import SszArm.CodecMeasureProvenanceEffects

namespace SszArm.Codec.Measure.Provenance

open SszNative (NatOperand)
open SszNative.Codec (Desc Value)
open SszNative.CodecMeasure
open Delimited (Span Protected)

 theorem bind_effects {α β : Type} {writes : List Span} (first : Outcome α)
    (next : α → Nat → Outcome β) (before : EffectsOwned writes first.effects)
    (after : ∀ value, first.result = .ok value → EffectsOwned writes (next value first.used).effects) :
    EffectsOwned writes (bind first next).effects := by
  cases result : first.result with
  | error reason => simpa only [bind, result] using before
  | ok value =>
      simpa only [bind, result] using
        (effectsOwned_append writes first.effects (next value first.used).effects).2 ⟨before, after value result⟩

 theorem primitive_effects_owned (writes : List Span) (arena : SszNative.Delimited.ArenaState)
    (shape : SszNative.Serialize.Desc) (logical : Value)
    (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used)) :
    EffectsOwned writes (primitive shape logical arena).effects := by
  intro effect member
  simp only [primitive, List.mem_singleton] at member
  subst effect
  intro call inCalls allocation allocated
  obtain ⟨low, high⟩ := (SszArm.Measure.resource_measure arena shape logical.toPrimitive).allocations
    call inCalls allocation allocated
  refine ⟨Nat.le_trans high storage, ?_⟩
  apply Serialize.protected_subspan_of_bounds free low
  by_cases empty : arena.capacity ≤ arena.used
  · have length := SszArm.Measure.callsTwo_measure arena shape logical.toPrimitive call inCalls allocation allocated
    omega
  · omega

 theorem add_effects_owned (writes : List Span) (arena : SszNative.Delimited.ArenaState)
    (left right : NatOperand) (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used)) :
    EffectsOwned writes (add left right arena).effects := by
  intro effect member
  simp only [add, List.mem_singleton] at member
  subst effect
  intro allocation allocated
  obtain ⟨checks, pointer, _cursor, _length⟩ :=
    SszNative.NatAdd.allocation_geometry left right arena.base arena.capacity arena.used allocation allocated
  have low := SszNative.Arena.used_le_start arena.base arena.used
  have high := checks.2.2.2.2.2
  dsimp [SszNative.Arena.finish] at high
  refine ⟨by omega, ?_⟩
  apply Serialize.protected_subspan_of_bounds free
  · omega
  · omega

 theorem writePlan_effects_owned {writes : List Span} (allocation : Option SszNative.Arena.Reservation)
    (index : Nat) (plan : Plan) (used : Nat)
    (stored : Storage.PlanBackingsProtected writes plan)
    (root : ∀ reservation, allocation = some reservation →
      Protected writes (reservation.pointer + 40 * index) 40) :
    EffectsOwned writes (writePlan allocation index plan used).effects := by
  cases allocation with
  | none => exact effectsOwned_nil writes
  | some reservation =>
      intro effect member
      simp only [writePlan, List.mem_singleton] at member
      subst effect
      exact ⟨root reservation rfl, stored⟩

 theorem reservePlans_effects_owned (writes : List Span) (count : Nat)
    (arena : SszNative.Delimited.ArenaState) : EffectsOwned writes (reservePlans count arena).effects := by
  unfold reservePlans
  split <;> intro effect member <;> simp only [List.mem_singleton] at member <;> subst effect <;> trivial

 theorem accumulate_effects_owned (writes : List Span) (arena : SszNative.Delimited.ArenaState)
    (inline : Bool) (child : Plan) (totals : Partial)
    (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used)) :
    EffectsOwned writes (accumulate inline child totals arena).effects := by
  unfold accumulate
  apply bind_effects
  · exact add_effects_owned writes arena _ _ storage free
  · intro leading _
    cases inline with
    | true => exact effectsOwned_nil writes
    | false =>
        apply bind_effects
        · exact add_effects_owned writes _ _ _ storage
            (Serialize.free_protected_after arena free _ (add_cursorSafe _ _ arena).1)
        · intro bodies _
          exact effectsOwned_nil writes

 theorem finishParts_effects_owned (writes : List Span) (arena : SszNative.Delimited.ArenaState)
    (parts : Parts) (values : List Value) (totals : Partial)
    (allocation : Option SszNative.Arena.Reservation)
    (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used)) :
    EffectsOwned writes (finishParts parts values totals allocation arena).effects := by
  unfold finishParts
  split
  · apply bind_effects
    · exact add_effects_owned writes arena _ _ storage free
    · intro size _
      apply bind_effects
      · rw [(compositeSize_resources size _).2]
        exact effectsOwned_nil writes
      · intro _ _
        apply bind_effects
        · rw [(hostSize_resources totals.leading _).2]
          exact effectsOwned_nil writes
        · intro _ _
          exact effectsOwned_nil writes
  · exact effectsOwned_nil writes

end SszArm.Codec.Measure.Provenance

import SszArm.CodecMeasureProvenanceEffectsLoop

namespace SszArm.Codec.Measure.Provenance

open SszNative.Codec (Desc Value)
open SszNative.CodecMeasure
open Delimited (Span Protected)

 theorem measureParts_effects_owned (writes : List Span) (source : Desc → Prop)
    (parts : Parts) (values : List Value) (visit : Visit values)
    (arena : SszNative.Delimited.ArenaState) (retain : Bool)
    (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (schemas : PartsSource source parts)
    (visitOwned : ∀ child member shape arena retain, source shape →
      arena.base + arena.capacity ≤ 2^64 →
      Protected writes (arena.base + arena.used) (arena.capacity - arena.used) →
      ResultOwned writes (Storage.PlanBackingsProtected writes) (visit child member shape arena retain).result)
    (visitEffects : ∀ child member shape arena retain, source shape →
      arena.base + arena.capacity ≤ 2^64 →
      Protected writes (arena.base + arena.used) (arena.capacity - arena.used) →
      EffectsOwned writes (visit child member shape arena retain).effects)
    (visitMono : ∀ child member shape arena retain,
      CursorSafe arena (visit child member shape arena retain).used) :
    EffectsOwned writes (measureParts parts values visit arena retain).effects := by
  unfold measureParts
  dsimp only
  split
  · apply bind_effects
    · exact reservePlans_effects_owned writes _ arena
    · intro allocation returned
      have records : Protected writes allocation.pointer (40 * parts.paired values) := by
        simpa only [returned, ResultOwned] using reservePlans_owned writes arena (parts.paired values) free
      have nextFree := Serialize.free_protected_after arena free _ (reservePlans_cursorSafe _ arena).1
      apply bind_effects
      · apply measureLoop_effects_owned writes source parts values visit _ _ 0 initial _
          storage nextFree schemas
        · intro reservation same
          cases same
          simpa only [Nat.mul_zero, Nat.add_zero] using records
        · exact visitOwned
        · exact visitEffects
        · exact visitMono
      · intro totals _
        apply finishParts_effects_owned writes _ parts values totals (some allocation) storage
        exact Serialize.free_protected_after _ nextFree _
          (measureLoop_cursorSafe parts values visit _ _ 0 initial _ visitMono).1
  · apply bind_effects
    · apply measureLoop_effects_owned writes source parts values visit _ _ 0 initial arena
        storage free schemas
      · intro reservation impossible
        cases impossible
      · exact visitOwned
      · exact visitEffects
      · exact visitMono
    · intro totals _
      apply finishParts_effects_owned writes _ parts values totals none storage
      exact Serialize.free_protected_after arena free _
        (measureLoop_cursorSafe parts values visit _ _ 0 initial arena visitMono).1

 theorem unionPlan_effects_owned (writes : List Span) (arena : SszNative.Delimited.ArenaState)
    (child : Plan) (retain : Bool) (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (stored : Storage.PlanBackingsProtected writes child) :
    EffectsOwned writes (unionPlan child arena retain).effects := by
  unfold unionPlan
  apply bind_effects
  · exact add_effects_owned writes arena child.size (.small 1) storage free
  · intro size _
    have nextFree := Serialize.free_protected_after arena free _ (add_cursorSafe child.size (.small 1) arena).1
    split
    · apply bind_effects
      · exact reservePlans_effects_owned writes 1 _
      · intro allocation returned
        have records : Protected writes allocation.pointer 40 := by
          simpa only [returned, ResultOwned, Nat.mul_one] using reservePlans_owned writes _ 1 nextFree
        apply bind_effects
        · apply writePlan_effects_owned _ 0 child _ stored
          intro reservation same
          cases same
          simpa only [Nat.mul_zero, Nat.add_zero] using records
        · intro _ _
          exact effectsOwned_nil writes
    · exact effectsOwned_nil writes

end SszArm.Codec.Measure.Provenance

import SszArm.CodecMeasureProvenanceEffectsStep

namespace SszArm.Codec.Measure.Provenance

open SszNative.Codec (Desc Value)
open SszNative.CodecMeasure
open Delimited (Span Protected)

/-- Protection of every committed initialized effect, even when a later child,
addition, host narrowing or arena reservation fails. No padding initialization
or rollback is inferred from the allocated range. -/
theorem measure_effects_owned (writes : List Span) (original : ArmState)
    (shape : Desc) (logical : Value) (arena : SszNative.Delimited.ArenaState) (retain : Bool)
    (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (schema : DescSource writes original shape) (value : ValueSource writes original logical) :
    EffectsOwned writes (measure shape logical arena retain).effects := by
  rw [measure]
  apply measureStep_effects_owned writes original shape logical arena retain _ storage free schema value
  · intro child member desc nextArena nextRetain source bounded nextFree
    exact measure_owned writes original desc child nextArena nextRetain bounded nextFree source
      (child_sources value child member)
  · intro child member desc nextArena nextRetain source bounded nextFree
    exact measure_effects_owned writes original desc child nextArena nextRetain bounded nextFree source
      (child_sources value child member)
  · intro child member desc nextArena nextRetain
    exact measure_cursorSafe desc child nextArena nextRetain
termination_by logical.nesting
decreasing_by exact Value.child_nesting_lt _ _ (by assumption)

 theorem measured_effects_owned {writes : List Span} {original : ArmState}
    {descAddress valueAddress : Nat} {shape : Desc} {logical : Value}
    {arena : SszNative.Delimited.ArenaState} {retain : Bool}
    (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (schema : Storage.DescOwned writes original descAddress shape)
    (value : Storage.ValueOwned writes original valueAddress logical) :
    EffectsOwned writes (measure shape logical arena retain).effects :=
  measure_effects_owned writes original shape logical arena retain storage free
    ⟨descAddress, schema⟩ ⟨valueAddress, value⟩

end SszArm.Codec.Measure.Provenance

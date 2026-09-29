import SszArm.CodecMeasureProvenanceStep

namespace SszArm.Codec.Measure.Provenance

open SszNative.Codec (Desc Value Error)
open SszNative.CodecMeasure
open Delimited (Span Protected)

/-- Every modeled result obtains its borrowed storage from original immutable
inputs or committed arena reservations. This theorem includes all error outcomes;
there is no successful-measurement premise at this root. -/
theorem measure_owned (writes : List Span) (original : ArmState)
    (shape : Desc) (logical : Value) (arena : SszNative.Delimited.ArenaState) (retain : Bool)
    (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (schema : DescSource writes original shape) (value : ValueSource writes original logical) :
    ResultOwned writes (Storage.PlanBackingsProtected writes)
      (measure shape logical arena retain).result := by
  rw [measure]
  apply measureStep_owned writes original shape logical arena retain _ storage free schema value
  · intro child member desc nextArena nextRetain source bounded nextFree
    exact measure_owned writes original desc child nextArena nextRetain bounded nextFree source
      (child_sources value child member)
  · intro child member desc nextArena nextRetain
    exact measure_cursorSafe desc child nextArena nextRetain
termination_by logical.nesting
decreasing_by exact Value.child_nesting_lt _ _ (by assumption)

/-- Success-branch projection used after actual measurement has returned. The
final observations are upgraded with protection proved from original storage;
no desired machine result is assumed by an entry contract. -/
theorem measured_plan_owned {writes : List Span} {original final : ArmState}
    {descAddress valueAddress output : Nat} {shape : Desc} {logical : Value}
    {arena : SszNative.Delimited.ArenaState} {retain : Bool} {plan : Plan}
    (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (schema : Storage.DescOwned writes original descAddress shape)
    (value : Storage.ValueOwned writes original valueAddress logical)
    (root : Protected writes output 40)
    (success : (measure shape logical arena retain).result = .ok plan)
    (observed : Storage.PlanAt final output plan) : Storage.PlanOwned writes final output plan := by
  have owned := measure_owned writes original shape logical arena retain storage free
    ⟨descAddress, schema⟩ ⟨valueAddress, value⟩
  apply Storage.plan_owned plan observed root
  simpa only [success, ResultOwned] using owned

 theorem measured_error_owned {writes : List Span} {original : ArmState}
    {descAddress valueAddress : Nat} {shape : Desc} {logical : Value}
    {arena : SszNative.Delimited.ArenaState} {retain : Bool} {reason : Error}
    (storage : arena.base + arena.capacity ≤ 2^64)
    (free : Protected writes (arena.base + arena.used) (arena.capacity - arena.used))
    (schema : Storage.DescOwned writes original descAddress shape)
    (value : Storage.ValueOwned writes original valueAddress logical)
    (failed : (measure shape logical arena retain).result = .error reason) : ErrorOwned writes reason := by
  have owned := measure_owned writes original shape logical arena retain storage free
    ⟨descAddress, schema⟩ ⟨valueAddress, value⟩
  simpa only [failed, ResultOwned] using owned

end SszArm.Codec.Measure.Provenance

import SszArm.CodecSerializeContract
import SszArm.CodecStoragePhysical

namespace SszArm.Codec.Serialize

open SszNative.Codec (Desc Value Error)
open SszNative.CodecMeasure (Plan)

 theorem Owned.physical {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) : value.Physical :=
  Storage.ValueAt.physical (Storage.value_at owned.value_at)

 theorem measured_outcome (s : ArmState) (args : Args) (desc : Desc) (value : Value) :
    Measure.outcome s args.measure desc value = measured s args desc value := rfl

 theorem outcome_of_measure_error (s : ArmState) (args : Args) (desc : Desc) (value : Value)
    (reason : Error) (failed : (measured s args desc value).result = .error reason) :
    outcome s args desc value = ⟨.error (.returned reason),
      (measured s args desc value).used, (measured s args desc value).effects, []⟩ := by
  change (SszNative.CodecMeasure.measure desc value (arenaOf s args) true).result = _ at failed
  simp only [outcome, SszNative.CodecEmit.serialize, failed, measured]

 theorem host_size_success (plan : Plan) (used : Nat) (fits : plan.size.value < 2^64) :
    (SszNative.CodecMeasure.hostSize plan.size used).result = .ok plan.size.value := by
  simp only [SszNative.CodecMeasure.hostSize, SszNative.Serialize.hostSize, fits, ↓reduceIte,
    SszNative.Serialize.unchanged, Except.mapError]

 theorem outcome_of_host_failure (s : ArmState) (args : Args) (desc : Desc) (value : Value)
    (plan : Plan) (success : (measured s args desc value).result = .ok plan)
    (tooLarge : ¬ plan.size.value < 2^64) :
    outcome s args desc value = ⟨.error (.returned (.primitive .outputTooSmall)),
      (measured s args desc value).used, (measured s args desc value).effects, []⟩ := by
  change (SszNative.CodecMeasure.measure desc value (arenaOf s args) true).result = _ at success
  simp only [outcome, SszNative.CodecEmit.serialize, success, SszNative.CodecMeasure.hostSize,
    SszNative.Serialize.hostSize, tooLarge, ↓reduceIte, SszNative.Serialize.unchanged,
    Except.mapError, measured]

 theorem outcome_of_capacity_failure (s : ArmState) (args : Args) (desc : Desc) (value : Value)
    (plan : Plan) (success : (measured s args desc value).result = .ok plan)
    (host : plan.size.value < 2^64) (short : ¬ plan.size.value ≤ args.capacity.toNat) :
    outcome s args desc value = ⟨.error (.returned (.primitive .outputTooSmall)),
      (measured s args desc value).used, (measured s args desc value).effects, []⟩ := by
  change (SszNative.CodecMeasure.measure desc value (arenaOf s args) true).result = _ at success
  simp only [outcome, SszNative.CodecEmit.serialize, success, host_size_success plan _ host,
    short, ↓reduceIte, measured]

 theorem outcome_resources (s : ArmState) (args : Args) (desc : Desc) (value : Value) :
    (outcome s args desc value).used = (measured s args desc value).used ∧
      (outcome s args desc value).effects = (measured s args desc value).effects := by
  cases first : (SszNative.CodecMeasure.measure desc value (arenaOf s args) true).result with
  | error reason => simp only [outcome, SszNative.CodecEmit.serialize, first, measured, and_self]
  | ok plan =>
    cases converted : (SszNative.CodecMeasure.hostSize plan.size
        (SszNative.CodecMeasure.measure desc value (arenaOf s args) true).used).result with
    | error reason => simp only [outcome, SszNative.CodecEmit.serialize, first, converted, measured, and_self]
    | ok count =>
      unfold outcome SszNative.CodecEmit.serialize
      simp only [first, converted]
      split <;> exact ⟨rfl, rfl⟩

/-- Pinned bytes and private-emitter safety are derived from the actual measured
plan, not assumed at the original serialization entry. -/
theorem measured_emission (s : ArmState) (args : Args) (desc : Desc) (value : Value)
    (owned : Owned s args desc value) (plan : Plan)
    (success : (measured s args desc value).result = .ok plan)
    (host : plan.size.value < 2^64) :
    (SszNative.CodecEmit.emit desc value (some plan)
      ⟨args.output.toNat, plan.size.value⟩).result = .ok plan.size.value ∧
      ∃ bytes, Ssz.serialize desc.erase value.erase = .ok bytes ∧ bytes.size = plan.size.value ∧
        SszNative.CodecEmit.Encodes (SszNative.CodecEmit.emit desc value (some plan)
          ⟨args.output.toNat, plan.size.value⟩).writes args.output.toNat bytes :=
  SszNative.CodecEmit.measured_emits desc value (arenaOf s args) owned.physical plan
    plan.size.value args.output.toNat success (host_size_success plan _ host)

 theorem outcome_success (s : ArmState) (args : Args) (desc : Desc) (value : Value)
    (owned : Owned s args desc value) (plan : Plan)
    (success : (measured s args desc value).result = .ok plan)
    (host : plan.size.value < 2^64) (fitting : plan.size.value ≤ args.capacity.toNat) :
    (outcome s args desc value).result = .ok plan.size.value := by
  have emitted := (SszNative.CodecEmit.measured_emits desc value (arenaOf s args)
    owned.physical plan plan.size.value 0 success (host_size_success plan _ host)).1
  change (SszNative.CodecMeasure.measure desc value (arenaOf s args) true).result = _ at success
  simp only [outcome, SszNative.CodecEmit.serialize, success, host_size_success plan _ host,
    fitting, ↓reduceIte, emitted]

end SszArm.Codec.Serialize

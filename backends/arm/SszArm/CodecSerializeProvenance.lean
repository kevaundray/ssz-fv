import SszArm.CodecSerializeOwnership
import SszArm.CodecMeasureProvenanceCommitted

namespace SszArm.Codec.Serialize

open SszNative.Codec (Desc Value Error)
open Delimited (Span Protected)

 theorem local_envelope_covered (s : ArmState) (args : Args) (desc : Desc) :
    BitVector.Covers (envelope s args desc) (stackSpans args desc ++ externalSpans args) := by
  intro span member
  exact ⟨span, List.mem_append.mpr (Or.inl member), Nat.le_refl _, Nat.le_refl _⟩

 theorem Owned.local_free {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) {writes : List Span}
    (cover : BitVector.Covers (stackSpans args desc ++ externalSpans args) writes) :
    Protected writes (freeSpan s args).1 (freeSpan s args).2 := by
  apply BitVector.Covers.protected (owned := owned.freeOwned)
  intro span member
  obtain ⟨outer, included, lower, upper⟩ := cover span member
  exact ⟨outer, List.mem_append.mpr (Or.inl included), lower, upper⟩

 theorem Owned.error_operands {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) {writes : List Span}
    (cover : BitVector.Covers (stackSpans args desc ++ externalSpans args) writes)
    {reason : Error} (failed : (measured s args desc value).result = .error reason) :
    Measure.Provenance.ErrorOwned writes reason := by
  have allWrites := (local_envelope_covered s args desc).trans cover
  have schema := Storage.Image.weaken _ (fun _ _ separated => allWrites.protected separated)
    owned.descriptor
  have logical := Storage.Image.weaken _ (fun _ _ separated => allWrites.protected separated)
    owned.value_at
  exact Measure.Provenance.measured_error_owned owned.storageBound
    (owned.local_free cover) schema logical failed

 theorem Owned.effects_owned {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) {writes : List Span}
    (cover : BitVector.Covers (stackSpans args desc ++ externalSpans args) writes) :
    Measure.Provenance.EffectsOwned writes (measured s args desc value).effects := by
  have allWrites := (local_envelope_covered s args desc).trans cover
  have schema := Storage.Image.weaken _ (fun _ _ separated => allWrites.protected separated)
    owned.descriptor
  have logical := Storage.Image.weaken _ (fun _ _ separated => allWrites.protected separated)
    owned.value_at
  exact Measure.Provenance.measured_effects_owned owned.storageBound
    (owned.local_free cover) schema logical

end SszArm.Codec.Serialize

import SszCodecEmitProofs
import SszX86.EmitModel

set_option autoImplicit false

namespace SszX86.CodecEmit
open SszNative

/-- The private emitter consumes a past measurement witness. An absent runtime
plan is permitted for fixed children; discarded plans remain logical witnesses,
not fabricated memory. No execution or semantic-validation result is a field. -/
structure GeneratedCall (desc : Codec.Desc) (value : Codec.Value)
    (supplied : Option CodecMeasure.Plan) (capacity : Nat) where
  retain : Bool
  measured : CodecMeasure.Plan
  generated : SszNative.CodecEmit.Generated desc value retain measured
  usable : retain = true ∨ FixedSize.isFixed desc = true
  children : SszNative.CodecEmit.children supplied = measured.children
  leading : measured.children ≠ [] →
    SszNative.CodecEmit.leading supplied = measured.leading
  fits : measured.size.value ≤ capacity
  host : capacity < 2 ^ 64

namespace GeneratedCall

/-- The eventual serialize caller derives this invariant from its completed
measurement and host/output guards. It does not assume schema validation. -/
def of_measure (desc : Codec.Desc) (value : Codec.Value)
    (arena : Delimited.ArenaState) (physical : value.Physical)
    (plan : CodecMeasure.Plan)
    (measured : (CodecMeasure.measure desc value arena true).result = .ok plan)
    (capacity : Nat) (fits : plan.size.value ≤ capacity) (host : capacity < 2 ^ 64) :
    GeneratedCall desc value (some plan) capacity :=
  ⟨true, plan, SszNative.CodecEmit.measure_generated desc value arena true physical plan measured,
    Or.inl rfl, rfl, fun _ => rfl, fits, host⟩

theorem result {desc : Codec.Desc} {value : Codec.Value}
    {supplied : Option CodecMeasure.Plan} {capacity : Nat}
    (h : GeneratedCall desc value supplied capacity) (address : Nat) :
    (SszNative.CodecEmit.emit desc value supplied ⟨address, capacity⟩).result =
      .ok h.measured.size.value :=
  SszNative.CodecEmit.generated_emit_success desc value h.retain h.measured supplied
    ⟨address, capacity⟩ h.generated h.usable h.children h.leading h.fits h.host

theorem encodes {desc : Codec.Desc} {value : Codec.Value}
    {supplied : Option CodecMeasure.Plan} {capacity : Nat}
    (h : GeneratedCall desc value supplied capacity) (address : Nat) (bytes : Ssz.Bytes)
    (semantic : Ssz.serialize desc.erase value.erase = .ok bytes) :
    SszNative.CodecEmit.Encodes
      (SszNative.CodecEmit.emit desc value supplied ⟨address, capacity⟩).writes address bytes :=
  SszNative.CodecEmit.generated_emit_encodes desc value h.retain h.measured supplied
    ⟨address, capacity⟩ bytes h.generated h.usable h.children h.leading h.fits h.host semantic

/-- The immutable seven-shape provider's logical precondition is a consequence
of the generated-plan invariant, not a new public validation shortcut. -/
theorem primitive_valid {shape : Serialize.Desc} {value : Codec.Value}
    {supplied : Option CodecMeasure.Plan} {capacity : Nat}
    (h : GeneratedCall (.primitive shape) value supplied capacity) :
    Emit.ValidCall shape value.toPrimitive capacity h.measured.size.value := by
  rcases h with ⟨retain, plan, generated, usable, children, leading, fits, host⟩
  have expected : Serialize.expectedSize shape value.toPrimitive =
      .ok plan.size.value := by
    cases generated with
    | primitive shape value retain size semantic => exact semantic
    | parts desc parts values retain plan plans front back shape => cases shape
  exact ⟨expected, Nat.lt_of_le_of_lt fits host, fits⟩

end GeneratedCall
end SszX86.CodecEmit

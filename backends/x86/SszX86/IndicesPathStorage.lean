import SszX86.IndicesStorage

set_option autoImplicit false

namespace SszX86.Indices.Storage
open SszNative

/-- Actual four-way jump-table order at resolve_step's original dispatch. -/
def pathStepTag : SszNative.Indices.PathStep → Nat
  | .position _ => 0
  | .length => 1
  | .activeFields => 2
  | .selector => 3

/-- PathStep occupies24 bytes aligned to8; only Position has an active Nat.
Padding stays opaque and is not asserted initialized by this observation. -/
structure PathStepAt (m : DataMem) (readonly : Codec.Footprint) (pointer : BitVec 64)
    (step : SszNative.Indices.PathStep) : Prop where
  header : Codec.HeaderAt m readonly pointer 24 8 8 (pathStepTag step : Int)
  ordinal : match step with
    | .position value => Codec.NatAt m readonly (pointer + 8) value
    | _ => True

theorem PathStepAt.frame {m n : DataMem} {readonly writes : Codec.Footprint}
    {pointer : BitVec 64} {step : SszNative.Indices.PathStep}
    (stored : PathStepAt m readonly pointer step)
    (frame : Codec.MemoryFrame m n writes)
    (separate : ∀ address, readonly address → ¬ writes address) :
    PathStepAt n readonly pointer step := by
  refine ⟨stored.header.frame frame separate, ?_⟩
  cases step with
  | position ordinal => exact stored.ordinal.frame frame separate
  | length | activeFields | selector => trivial

/-- Bounds are on the physical path slice, never on logical ordinal metadata. -/
structure PathArrayAt (m : DataMem) (readonly : Codec.Footprint) (pointer : BitVec 64)
    (steps : List SszNative.Indices.PathStep) : Prop where
  countBound : steps.length < 2 ^ 64
  byteBound : 24 * steps.length < 2 ^ 63
  span : Codec.Span readonly pointer (24 * steps.length) 8
  elements : ∀ (i : Nat) (inside : i < steps.length),
    PathStepAt m readonly (pointer + BitVec.ofNat 64 (24 * i)) steps[i]

theorem PathArrayAt.frame {m n : DataMem} {readonly writes : Codec.Footprint}
    {pointer : BitVec 64} {steps : List SszNative.Indices.PathStep}
    (stored : PathArrayAt m readonly pointer steps)
    (frame : Codec.MemoryFrame m n writes)
    (separate : ∀ address, readonly address → ¬ writes address) :
    PathArrayAt n readonly pointer steps := by
  refine ⟨stored.countBound, stored.byteBound, stored.span, ?_⟩
  intro i inside
  exact (stored.elements i inside).frame frame separate

end SszX86.Indices.Storage

import SszX86.CodecStorage
import SszX86.MeasureCore

set_option autoImplicit false

namespace SszX86.Codec
open SszNative UintCodec

/-- Convert the checked unsigned observation interface back to the actual byte
load, while obtaining its footprint from the enclosing physical object. -/
theorem LoadAt.of_widthLoad {m : DataMem} {r : Footprint} {p : BitVec 64}
    {total alignment : Nat} (span : Span r p total alignment)
    (off bytes value : Nat) (within : off + bytes ≤ total)
    (stored : widthLoad m (p.toNat + off) bytes = some value) :
    LoadAt m r (p + BitVec.ofNat 64 off) bytes (value : Int) := by
  refine ⟨?_, ?_⟩
  · simpa only [width_address] using widthLoad_eq m (p.toNat + off) bytes value stored
  · intro a ha
    exact span.covered a (Emit.span_shift p off bytes total within ha)

/-- The old primitive provider's successful result initializes exactly a leaf
Plan. Its status word is consumed by that provider; padding is not assumed here.
The borrowed operand remains representation-exact, including redundant limbs. -/
theorem PlanAt.of_primitive {m : DataMem} {r : Footprint} {p : BitVec 64}
    {size : NatOperand} (old : Measure.PlanAt (widthLoad m) p.toNat size)
    (span : Span r p 40 8) (borrowed : ∀ a, Emit.NatBorrowed size a → r a) :
    PlanAt m r p (CodecMeasure.Plan.leaf size) := by
  have bound := span.bound
  have sizePointer : (p + 16).toNat = p.toNat + 16 := by bv_omega
  have sizeSpan : Span r (p + 16) 16 8 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [sizePointer]
      omega
    · rw [sizePointer, Nat.add_mod, span.aligned]
      decide
    · rw [sizePointer]
      omega
    · intro a ha
      exact span.covered a (Emit.span_shift p 16 16 40 (by decide) ha)
  apply Stored.plan span (by decide)
  · refine ⟨?_, ?_, by decide, by decide, ?_⟩
    · have pointer := LoadAt.of_widthLoad span 0 8 8 (by decide)
        (by simpa only [Nat.add_zero] using old.1)
      simpa only [BitVec.add_zero] using pointer
    · exact LoadAt.of_widthLoad span 8 8 0 (by decide) old.2.1
    · refine ⟨by decide, by decide, by decide, ?_⟩
      intro a ha
      rcases ha with ⟨i, hi, equal⟩
      omega
  · refine ⟨?_, sizeSpan, borrowed⟩
    change widthLoad m (p + 16).toNat 8 = some size.pointer.toNat ∧
      widthLoad m ((p + 16).toNat + 8) 8 = some size.payload.toNat ∧ size.At (widthLoad m)
    rw [sizePointer]
    exact old.2.2.1
  · exact LoadAt.of_widthLoad span 32 8 0 (by decide) old.2.2.2.1
  · exact .plansNil

end SszX86.Codec

import SszX86.CodecStorage
import SszIndicesTypes

set_option autoImplicit false

namespace SszX86.Indices.Storage
open SszNative

/-- The actual borrowed Nat array. Its extent is physical, not a bound on the
logical natural numbers stored in it. Readonly arrays and limb slices may alias. -/
structure NatArrayAt (m : DataMem) (readonly : Codec.Footprint) (pointer : BitVec 64)
    (values : List NatOperand) : Prop where
  countBound : values.length < 2 ^ 64
  byteBound : 16 * values.length < 2 ^ 63
  span : Codec.Span readonly pointer (16 * values.length) 8
  elements : ∀ (i : Nat) (inside : i < values.length),
    Codec.NatAt m readonly (pointer + BitVec.ofNat 64 (16 * i)) values[i]

/-- A memory frame transports every original borrowed limb, including trailing
zero limbs and an empty Large representation, without imposing disjoint inputs. -/
theorem NatArrayAt.frame {m n : DataMem} {readonly writes : Codec.Footprint}
    {pointer : BitVec 64} {values : List NatOperand}
    (stored : NatArrayAt m readonly pointer values)
    (frame : Codec.MemoryFrame m n writes)
    (separate : ∀ address, readonly address → ¬ writes address) :
    NatArrayAt n readonly pointer values := by
  refine ⟨stored.countBound, stored.byteBound, stored.span, ?_⟩
  intro i inside
  exact (stored.elements i inside).frame frame separate

/-- A fat pointer to a Nat array reuses the codec's physical slice convention. -/
structure NatSliceAt (m : DataMem) (readonly : Codec.Footprint)
    (field pointer : BitVec 64) (values : List NatOperand) : Prop where
  slice : Codec.SliceAt m readonly field pointer values.length 16 8
  elements : NatArrayAt m readonly pointer values

theorem NatSliceAt.frame {m n : DataMem} {readonly writes : Codec.Footprint}
    {field pointer : BitVec 64} {values : List NatOperand}
    (stored : NatSliceAt m readonly field pointer values)
    (frame : Codec.MemoryFrame m n writes)
    (separate : ∀ address, readonly address → ¬ writes address) :
    NatSliceAt n readonly field pointer values :=
  ⟨stored.slice.frame frame separate, stored.elements.frame frame separate⟩

end SszX86.Indices.Storage

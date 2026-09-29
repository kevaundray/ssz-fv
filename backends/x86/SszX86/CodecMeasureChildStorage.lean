import SszX86.CodecEmitPartsStorage

set_option autoImplicit false

namespace SszX86.CodecMeasureChild
open SszNative
open SszX86.Codec

/-- Addresses captured by the actual private initializer closure. `leading` and
`bodies` are separate mutable Nat objects; neither belongs to the immutable
capture footprint merely because its pointer is stored there. -/
structure Capture where
  parts : BitVec 64
  values : BitVec 64
  keep : BitVec 64
  allFixed : BitVec 64
  leading : BitVec 64
  bodies : BitVec 64

/-- The native capture object is seven words (56 bytes). All fields here are
reads performed by the actual closure; no future child result is required. -/
structure CaptureAt (m : DataMem) (r : Footprint) (p : BitVec 64) (capture : Capture)
    (parts : SszNative.CodecMeasure.Parts) (values : List SszNative.Codec.Value)
    (keep : Bool) : Prop where
  span : Span r p 56 8
  partsPointer : LoadAt m r p 8 (capture.parts.toNat : Int)
  partsStored : CodecEmitParts.PartsAt m r capture.parts parts
  valuesSlice : SliceAt m r (p + 8) capture.values values.length 48 16
  valuesStored : ValuesAt m r capture.values values
  keepPointer : LoadAt m r (p + 24) 8 (capture.keep.toNat : Int)
  keepStored : LoadAt m r capture.keep 1 (if keep then 1 else 0)
  fixedPointer : LoadAt m r (p + 32) 8 (capture.allFixed.toNat : Int)
  fixedStored : LoadAt m r capture.allFixed 1 (if parts.allFixed then 1 else 0)
  leadingPointer : LoadAt m r (p + 40) 8 (capture.leading.toNat : Int)
  bodiesPointer : LoadAt m r (p + 48) 8 (capture.bodies.toNat : Int)

theorem CaptureAt.frame {m n : DataMem} {r w : Footprint} {p : BitVec 64}
    {capture : Capture} {parts : SszNative.CodecMeasure.Parts}
    {values : List SszNative.Codec.Value} {keep : Bool}
    (stored : CaptureAt m r p capture parts values keep)
    (frame : MemoryFrame m n w) (separate : ∀ a, r a → ¬ w a) :
    CaptureAt n r p capture parts values keep :=
  ⟨stored.span, stored.partsPointer.frame frame separate,
    stored.partsStored.frame frame separate, stored.valuesSlice.frame frame separate,
    stored.valuesStored.frame frame separate, stored.keepPointer.frame frame separate,
    stored.keepStored.frame frame separate, stored.fixedPointer.frame frame separate,
    stored.fixedStored.frame frame separate, stored.leadingPointer.frame frame separate,
    stored.bodiesPointer.frame frame separate⟩

/-- Accumulator storage is independent of the immutable closure footprint. It
can be transported across the recursive child and then updated by real adds. -/
structure PartialAt (m : DataMem) (r : Footprint) (capture : Capture)
    (totals : SszNative.CodecMeasure.Partial) : Prop where
  leading : NatAt m r capture.leading totals.leading
  bodies : NatAt m r capture.bodies totals.bodies

theorem PartialAt.frame {m n : DataMem} {r w : Footprint} {capture : Capture}
    {totals : SszNative.CodecMeasure.Partial} (stored : PartialAt m r capture totals)
    (frame : MemoryFrame m n w) (separate : ∀ a, r a → ¬ w a) :
    PartialAt n r capture totals :=
  ⟨stored.leading.frame frame separate, stored.bodies.frame frame separate⟩

/-- Both real panic bounds follow from the paired-prefix loop invariant, even
when the field/value lengths mismatch. Arity equality is deliberately absent. -/
theorem paired_index (parts : SszNative.CodecMeasure.Parts)
    (values : List SszNative.Codec.Value) (index : Nat)
    (bound : index < parts.paired values) :
    index < values.length ∧
      (∀ fields, parts = .fields fields → index < fields.length) := by
  cases parts with
  | repeated element =>
    refine ⟨bound, ?_⟩
    intro fields equal
    cases equal
  | fields fields =>
    simp only [SszNative.CodecMeasure.Parts.paired, Nat.lt_min] at bound
    refine ⟨bound.2, ?_⟩
    intro other equal
    cases equal
    exact bound.1

/-- Indexing the capture gives the actual recursively represented Value, not
merely its enum tag; the borrowed children may share storage with descriptors. -/
theorem CaptureAt.value_at {m : DataMem} {r : Footprint} {p : BitVec 64}
    {capture : Capture} {parts : SszNative.CodecMeasure.Parts}
    {values : List SszNative.Codec.Value} {keep : Bool}
    (stored : CaptureAt m r p capture parts values keep) (index : Nat)
    (bound : index < parts.paired values) :
    ValueAt m r (capture.values + BitVec.ofNat 64 (48 * index))
      values[index]'(paired_index parts values index bound).1 := by
  exact CodecEmitParts.value_at_index stored.valuesStored index _
    (List.getElem?_eq_getElem (paired_index parts values index bound).1)

end SszX86.CodecMeasureChild

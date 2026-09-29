import SszX86.CodecStorageBase

set_option autoImplicit false

namespace SszX86.Codec
open SszNative UintCodec

structure HeaderAt (m : DataMem) (r : Footprint) (p : BitVec 64)
    (bytes alignment tagBytes : Nat) (discriminant : Int) : Prop where
  span : Span r p bytes alignment
  tag : LoadAt m r p tagBytes discriminant

theorem HeaderAt.frame {m n : DataMem} {r w : Footprint} {p : BitVec 64}
    {bytes alignment tagBytes : Nat} {tag : Int}
    (h : HeaderAt m r p bytes alignment tagBytes tag)
    (frame : MemoryFrame m n w) (separate : ∀ a, r a → ¬ w a) :
    HeaderAt n r p bytes alignment tagBytes tag := ⟨h.span, h.tag.frame frame separate⟩

/-- Indices of physical storage, not a second codec semantic model. In particular,
all recursive values, descriptor metadata and retained plans are the shared types. -/
inductive StorageObject where
  | desc (p : BitVec 64) (desc : SszNative.Codec.Desc)
  | fields (p : BitVec 64) (fields : List (String × SszNative.Codec.Desc))
  | variants (p : BitVec 64) (variants : List (NatOperand × SszNative.Codec.Desc))
  | flags (p : BitVec 64) (active : List Bool)
  | value (p : BitVec 64) (value : SszNative.Codec.Value)
  | values (p : BitVec 64) (values : List SszNative.Codec.Value)
  | plan (p : BitVec 64) (plan : CodecMeasure.Plan)
  | plans (p : BitVec 64) (plans : List CodecMeasure.Plan)

/-- Finite recursive observations in one shared readonly footprint. No separation
between inputs is required. Only active enum fields and borrowed bytes are read;
physical spans also protect opaque padding from writes by the callee. -/
inductive Stored (m : DataMem) (r : Footprint) : StorageObject → Prop where
  | descPrimitive {p : BitVec 64} {d : SszNative.Serialize.Desc} :
      PrimitiveDescAt m r p d → Stored m r (.desc p (.primitive d))
  | descVector {p child : BitVec 64} {d : SszNative.Codec.Desc} {length : NatOperand} :
      HeaderAt m r p 40 8 8 7 → NatAt m r (p + 8) length →
      LoadAt m r (p + 24) 8 (child.toNat : Int) → Stored m r (.desc child d) →
      Stored m r (.desc p (.vector d length))
  | descList {p child : BitVec 64} {d : SszNative.Codec.Desc} {limit : NatOperand} :
      HeaderAt m r p 40 8 8 8 → NatAt m r (p + 8) limit →
      LoadAt m r (p + 24) 8 (child.toNat : Int) → Stored m r (.desc child d) →
      Stored m r (.desc p (.list d limit))
  | descProgressiveList {p child : BitVec 64} {d : SszNative.Codec.Desc}
      {limit : Option NatOperand} :
      HeaderAt m r p 40 8 8 9 → LoadAt m r (p + 8) 8 (child.toNat : Int) →
      OptionNatAt m r (p + 16) limit → Stored m r (.desc child d) →
      Stored m r (.desc p (.progressiveList d limit))
  | descContainer {p fields : BitVec 64} {ds : List (String × SszNative.Codec.Desc)} :
      HeaderAt m r p 40 8 8 10 → SliceAt m r (p + 8) fields ds.length 24 8 →
      Stored m r (.fields fields ds) → Stored m r (.desc p (.container ds))
  | descProgressiveContainer {p active fields : BitVec 64} {flags : List Bool}
      {ds : List (String × SszNative.Codec.Desc)} :
      HeaderAt m r p 40 8 8 11 → SliceAt m r (p + 8) active flags.length 1 1 →
      Stored m r (.flags active flags) → SliceAt m r (p + 24) fields ds.length 24 8 →
      Stored m r (.fields fields ds) →
      Stored m r (.desc p (.progressiveContainer flags ds))
  | descCompatibleUnion {p variants : BitVec 64}
      {ds : List (NatOperand × SszNative.Codec.Desc)} :
      HeaderAt m r p 40 8 8 12 → SliceAt m r (p + 8) variants ds.length 24 8 →
      Stored m r (.variants variants ds) → Stored m r (.desc p (.compatibleUnion ds))
  | fieldsNil {p : BitVec 64} : Stored m r (.fields p [])
  | fieldsCons {p namePointer child : BitVec 64} {name : String}
      {d : SszNative.Codec.Desc} {ds : List (String × SszNative.Codec.Desc)} :
      Span r p 24 8 → SliceAt m r p namePointer name.toUTF8.data.size 1 1 →
      BytesAt m r namePointer name.toUTF8.data →
      LoadAt m r (p + 16) 8 (child.toNat : Int) → Stored m r (.desc child d) →
      Stored m r (.fields (p + 24) ds) → Stored m r (.fields p ((name, d) :: ds))
  | variantsNil {p : BitVec 64} : Stored m r (.variants p [])
  | variantsCons {p child : BitVec 64} {selector : NatOperand}
      {d : SszNative.Codec.Desc} {ds : List (NatOperand × SszNative.Codec.Desc)} :
      Span r p 24 8 → LoadAt m r p 8 (child.toNat : Int) →
      NatAt m r (p + 8) selector → Stored m r (.desc child d) →
      Stored m r (.variants (p + 24) ds) → Stored m r (.variants p ((selector, d) :: ds))
  | flagsNil {p : BitVec 64} : Stored m r (.flags p [])
  | flagsCons {p : BitVec 64} {flag : Bool} {flags : List Bool} :
      LoadAt m r p 1 (if flag then 1 else 0) → Stored m r (.flags (p + 1) flags) →
      Stored m r (.flags p (flag :: flags))
  | valueBool {p buffer : BitVec 64} {value : Bool} :
      PrimitiveValueAt m r p buffer (.bool value) → Stored m r (.value p (.bool value))
  | valueUint {p buffer : BitVec 64} {value : NatOperand} :
      PrimitiveValueAt m r p buffer (.uint value) → Stored m r (.value p (.uint value))
  | valueBytes {p buffer : BitVec 64} {value : Ssz.Bytes} :
      PrimitiveValueAt m r p buffer (.bytes value) → Stored m r (.value p (.bytes value))
  | valueBits {p buffer : BitVec 64} {value : SszNative.Serialize.Packed} :
      PrimitiveValueAt m r p buffer (.bits value) → Stored m r (.value p (.bits value))
  | valueSeq {p children : BitVec 64} {values : List SszNative.Codec.Value} :
      HeaderAt m r p 48 16 1 4 → SliceAt m r (p + 8) children values.length 48 16 →
      Stored m r (.values children values) → Stored m r (.value p (.seq values))
  | valueUnion {p child : BitVec 64} {selector : NatOperand} {value : SszNative.Codec.Value} :
      HeaderAt m r p 48 16 1 5 → NatAt m r (p + 8) selector →
      LoadAt m r (p + 24) 8 (child.toNat : Int) → Stored m r (.value child value) →
      Stored m r (.value p (.union selector value))
  | valuesNil {p : BitVec 64} : Stored m r (.values p [])
  | valuesCons {p : BitVec 64} {value : SszNative.Codec.Value}
      {values : List SszNative.Codec.Value} :
      Stored m r (.value p value) → Stored m r (.values (p + 48) values) →
      Stored m r (.values p (value :: values))
  | plan {p : BitVec 64} {plan : CodecMeasure.Plan} :
      Span r p 40 8 → plan.childrenPointer < 2 ^ 64 →
      SliceAt m r p (BitVec.ofNat 64 plan.childrenPointer) plan.children.length 40 8 →
      NatAt m r (p + 16) plan.size → LoadAt m r (p + 32) 8 (plan.leading : Int) →
      Stored m r (.plans (BitVec.ofNat 64 plan.childrenPointer) plan.children) →
      Stored m r (.plan p plan)
  | plansNil {p : BitVec 64} : Stored m r (.plans p [])
  | plansCons {p : BitVec 64} {plan : CodecMeasure.Plan} {plans : List CodecMeasure.Plan} :
      Stored m r (.plan p plan) → Stored m r (.plans (p + 40) plans) →
      Stored m r (.plans p (plan :: plans))

abbrev DescAt (m : DataMem) (r : Footprint) (p : BitVec 64) (d : SszNative.Codec.Desc) :=
  Stored m r (.desc p d)
abbrev FieldsAt (m : DataMem) (r : Footprint) (p : BitVec 64)
    (ds : List (String × SszNative.Codec.Desc)) := Stored m r (.fields p ds)
abbrev VariantsAt (m : DataMem) (r : Footprint) (p : BitVec 64)
    (ds : List (NatOperand × SszNative.Codec.Desc)) := Stored m r (.variants p ds)
abbrev ValueAt (m : DataMem) (r : Footprint) (p : BitVec 64) (v : SszNative.Codec.Value) :=
  Stored m r (.value p v)
abbrev ValuesAt (m : DataMem) (r : Footprint) (p : BitVec 64) (vs : List SszNative.Codec.Value) :=
  Stored m r (.values p vs)
abbrev PlanAt (m : DataMem) (r : Footprint) (p : BitVec 64) (plan : CodecMeasure.Plan) :=
  Stored m r (.plan p plan)
abbrev PlansAt (m : DataMem) (r : Footprint) (p : BitVec 64) (plans : List CodecMeasure.Plan) :=
  Stored m r (.plans p plans)

/-- Transport follows the entire finite borrowed graph, not only its root tag. -/
theorem Stored.frame {m n : DataMem} {r w : Footprint} {object : StorageObject}
    (h : Stored m r object) (frame : MemoryFrame m n w)
    (separate : ∀ a, r a → ¬ w a) : Stored n r object := by
  induction h <;> constructor <;>
    first
    | assumption
    | exact PrimitiveDescAt.frame ‹_› frame separate
    | exact PrimitiveValueAt.frame ‹_› frame separate
    | exact HeaderAt.frame ‹_› frame separate
    | exact NatAt.frame ‹_› frame separate
    | exact OptionNatAt.frame ‹_› frame separate
    | exact LoadAt.frame ‹_› frame separate
    | exact SliceAt.frame ‹_› frame separate
    | exact BytesAt.frame ‹_› frame separate

/-- Physical root bounds are available even for malformed schemas. -/
theorem DescAt.span {m : DataMem} {r : Footprint} {p : BitVec 64}
    {d : SszNative.Codec.Desc} (h : DescAt m r p d) : Span r p 40 8 := by
  cases h with
  | descPrimitive h => exact h.span
  | descVector h _ _ _ | descList h _ _ _ | descProgressiveList h _ _ _
  | descContainer h _ _ | descProgressiveContainer h _ _ _ _
  | descCompatibleUnion h _ _ => exact h.span

def descTag : SszNative.Codec.Desc → Nat
  | .primitive d => Emit.descTag d
  | .vector _ _ => 7
  | .list _ _ => 8
  | .progressiveList _ _ => 9
  | .container _ => 10
  | .progressiveContainer _ _ => 11
  | .compatibleUnion _ => 12

theorem DescAt.tag {m : DataMem} {r : Footprint} {p : BitVec 64}
    {d : SszNative.Codec.Desc} (h : DescAt m r p d) :
    Mem.loadInt m p 8 = some (descTag d : Int) := by
  cases h with
  | descPrimitive h => exact h.stored.1
  | descVector h _ _ _ | descList h _ _ _ | descProgressiveList h _ _ _
  | descContainer h _ _ | descProgressiveContainer h _ _ _ _
  | descCompatibleUnion h _ _ => exact h.tag.load

theorem ValueAt.span {m : DataMem} {r : Footprint} {p : BitVec 64}
    {v : SszNative.Codec.Value} (h : ValueAt m r p v) : Span r p 48 16 := by
  cases h with
  | valueBool h | valueUint h | valueBytes h | valueBits h => exact h.span
  | valueSeq h _ _ | valueUnion h _ _ _ => exact h.span

/-- Primitive callers recover their original complete live-field ABI relation. -/
theorem DescAt.primitive {m : DataMem} {r : Footprint} {p : BitVec 64}
    {d : SszNative.Serialize.Desc} (h : DescAt m r p (.primitive d)) : Emit.DescAt m p d := by
  cases h with
  | descPrimitive h => exact h.stored

/-- Decoder Slots contain only an active Option<Nat> plus two usize fields. -/
structure SlotAt (m : DataMem) (r : Footprint) (p : BitVec 64)
    (slot : CodecDecode.Slot) : Prop where
  span : Span r p 40 8
  «width» : OptionNatAt m r p slot.width
  start : LoadAt m r (p + 24) 8 (slot.start : Int)
  ending : LoadAt m r (p + 32) 8 (slot.ending : Int)

theorem SlotAt.frame {m n : DataMem} {r w : Footprint} {p : BitVec 64}
    {slot : CodecDecode.Slot} (h : SlotAt m r p slot)
    (frame : MemoryFrame m n w) (separate : ∀ a, r a → ¬ w a) : SlotAt n r p slot :=
  ⟨h.span, h.width.frame frame separate, h.start.frame frame separate,
    h.ending.frame frame separate⟩

end SszX86.Codec

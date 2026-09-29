import SszX86.CodecStorage
import SszCodecDecodeResourcesPhysical

set_option autoImplicit false

namespace SszX86.Codec
open SszNative UintCodec

/-- The static empty Value slice uses the measured Value alignment as its dangling
pointer. Reserved empty arrays retain their actual reservation pointer instead. -/
def decodedChildrenPointer : Option Arena.Reservation → Nat
  | none => 16
  | some allocation => allocation.pointer

inductive DecodedObject where
  | node (p : BitVec 64) (node : CodecDecode.Node)
  | nodes (p : BitVec 64) (nodes : List CodecDecode.Node)

/-- `source` is the original input base, not the current recursive window. Node
byte offsets and reservation addresses are those of the existing decoder model. -/
inductive DecodedStored (m : DataMem) (r : Footprint) (source : BitVec 64) :
    DecodedObject → Prop where
  | bool {p buffer : BitVec 64} {value : Bool} :
      PrimitiveValueAt m r p buffer (.bool value) → DecodedStored m r source (.node p (.bool value))
  | uint {p buffer : BitVec 64} {value : NatOperand} :
      PrimitiveValueAt m r p buffer (.uint value) → DecodedStored m r source (.node p (.uint value))
  | bytes {p : BitVec 64} {offset : Nat} {value : Ssz.Bytes} :
      source.toNat + offset + value.size ≤ 2 ^ 64 →
      PrimitiveValueAt m r p (source + BitVec.ofNat 64 offset) (.bytes value) →
      DecodedStored m r source (.node p (.bytes offset value))
  | bits {p : BitVec 64} {offset : Nat} {value : SszNative.Serialize.Packed} :
      source.toNat + offset + value.bytes.size ≤ 2 ^ 64 →
      PrimitiveValueAt m r p (source + BitVec.ofNat 64 offset) (.bits value) →
      DecodedStored m r source (.node p (.bits offset value))
  | seq {p : BitVec 64} {allocation : Option Arena.Reservation}
      {children : List CodecDecode.Node} :
      HeaderAt m r p 48 16 1 4 → decodedChildrenPointer allocation < 2 ^ 64 →
      (allocation = none → children = []) →
      SliceAt m r (p + 8) (BitVec.ofNat 64 (decodedChildrenPointer allocation))
        children.length 48 16 →
      DecodedStored m r source (.nodes (BitVec.ofNat 64 (decodedChildrenPointer allocation)) children) →
      DecodedStored m r source (.node p (.seq allocation children))
  | union {p : BitVec 64} {selector : NatOperand} {allocation : Arena.Reservation}
      {child : CodecDecode.Node} :
      HeaderAt m r p 48 16 1 5 → allocation.pointer < 2 ^ 64 →
      NatAt m r (p + 8) selector → LoadAt m r (p + 24) 8 (allocation.pointer : Int) →
      DecodedStored m r source (.node (BitVec.ofNat 64 allocation.pointer) child) →
      DecodedStored m r source (.node p (.union selector allocation child))
  | nil {p : BitVec 64} : DecodedStored m r source (.nodes p [])
  | cons {p : BitVec 64} {node : CodecDecode.Node} {nodes : List CodecDecode.Node} :
      DecodedStored m r source (.node p node) → DecodedStored m r source (.nodes (p + 48) nodes) →
      DecodedStored m r source (.nodes p (node :: nodes))

abbrev NodeAt (m : DataMem) (r : Footprint) (source p : BitVec 64) (node : CodecDecode.Node) :=
  DecodedStored m r source (.node p node)
abbrev NodesAt (m : DataMem) (r : Footprint) (source p : BitVec 64)
    (nodes : List CodecDecode.Node) := DecodedStored m r source (.nodes p nodes)

theorem DecodedStored.frame {m n : DataMem} {r w : Footprint} {source : BitVec 64}
    {object : DecodedObject} (h : DecodedStored m r source object)
    (frame : MemoryFrame m n w) (separate : ∀ a, r a → ¬ w a) :
    DecodedStored n r source object := by
  induction h <;> constructor <;>
    first
    | assumption
    | exact PrimitiveValueAt.frame ‹_› frame separate
    | exact HeaderAt.frame ‹_› frame separate
    | exact SliceAt.frame ‹_› frame separate
    | exact NatAt.frame ‹_› frame separate
    | exact LoadAt.frame ‹_› frame separate

def DecodedObject.values : DecodedObject → StorageObject
  | .node p node => .value p node.value
  | .nodes p nodes => .values p (CodecDecode.Node.values nodes)

/-- A decoded node supplies the same recursive Value ABI consumed by measurement
and emission; addresses are retained by the stronger source-indexed relation. -/
theorem DecodedStored.value {m : DataMem} {r : Footprint} {source : BitVec 64}
    {object : DecodedObject} (h : DecodedStored m r source object) :
    Stored m r object.values := by
  induction h with
  | bool h => exact .valueBool h
  | uint h => exact .valueUint h
  | bytes _ h => exact .valueBytes h
  | bits _ h => exact .valueBits h
  | seq header bound empty slice children ih =>
    apply Stored.valueSeq header
    · simpa only [CodecDecode.nodeValues_length] using slice
    · exact ih
  | union header bound selector pointer child ih =>
    apply Stored.valueUnion header selector
    · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] using pointer
    · exact ih
  | nil => exact .valuesNil
  | cons head tail ihHead ihTail => exact .valuesCons ihHead ihTail

theorem NodeAt.value {m : DataMem} {r : Footprint} {source p : BitVec 64}
    {node : CodecDecode.Node} (h : NodeAt m r source p node) : ValueAt m r p node.value :=
  DecodedStored.value h

theorem NodesAt.values {m : DataMem} {r : Footprint} {source p : BitVec 64}
    {nodes : List CodecDecode.Node} (h : NodesAt m r source p nodes) :
    ValuesAt m r p (CodecDecode.Node.values nodes) := DecodedStored.value h

theorem NodeAt.span {m : DataMem} {r : Footprint} {source p : BitVec 64}
    {node : CodecDecode.Node} (h : NodeAt m r source p node) : Span r p 48 16 := h.value.span

end SszX86.Codec

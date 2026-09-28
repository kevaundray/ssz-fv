import SszSerializeCore

set_option autoImplicit false

namespace SszNative.Codec

/- This mathematical representation is not an ISA execution proof. Inductive
values describe finite unfoldings of borrowed native trees, not ownership trees:
repeated logical children may be represented by the same immutable native
storage. There is no pointer layout, disjointness condition, depth limit, schema
validation, or successful-parse premise here. Every NatOperand retains its
original representation, including borrowed pointers and redundant high limbs.
Only erasure forgets that representation. -/

/-- The seven existing primitive shapes and all six native composite shapes.
Fields and variants are paired, ordered slices, as in native `Field`/`Variant`. -/
inductive Desc where
  | primitive (shape : Serialize.Desc)
  | vector (element : Desc) (length : NatOperand)
  | list (element : Desc) (limit : NatOperand)
  | progressiveList (element : Desc) (limit : Option NatOperand)
  | container (fields : List (String × Desc))
  | progressiveContainer (active : List Bool) (fields : List (String × Desc))
  | compatibleUnion (variants : List (NatOperand × Desc))

/-- Native values remain native recursively: in particular an integer or union
inside a sequence keeps its NatOperand, not merely its erased natural number. -/
inductive Value where
  | bool (value : Bool)
  | uint (number : NatOperand)
  | bytes (data : Ssz.Bytes)
  | bits (data : Serialize.Packed)
  | seq (values : List Value)
  | union (selector : NatOperand) (value : Value)

/-- Symbolic native enum tags, not a claim about ABI discriminant bytes. -/
inductive DescTag where
  | bool | uint | byteVector | byteList | bitVector | bitList | progressiveBitList
  | vector | list | progressiveList | container | progressiveContainer | compatibleUnion
  deriving DecidableEq, Repr

/-- The six symbolic native value tags, independently of their payloads. -/
inductive ValueTag where
  | bool | uint | bytes | bits | seq | union
  deriving DecidableEq, Repr

def primitiveTag : Serialize.Desc → DescTag
  | .bool => .bool
  | .uint _ => .uint
  | .byteVector _ => .byteVector
  | .byteList _ => .byteList
  | .bitVector _ => .bitVector
  | .bitList _ => .bitList
  | .progressiveBitList _ => .progressiveBitList

def Desc.tag : Desc → DescTag
  | .primitive shape => primitiveTag shape
  | .vector _ _ => .vector
  | .list _ _ => .list
  | .progressiveList _ _ => .progressiveList
  | .container _ => .container
  | .progressiveContainer _ _ => .progressiveContainer
  | .compatibleUnion _ => .compatibleUnion

def Value.tag : Value → ValueTag
  | .bool _ => .bool
  | .uint _ => .uint
  | .bytes _ => .bytes
  | .bits _ => .bits
  | .seq _ => .seq
  | .union _ _ => .union

def erasedDescTag : Ssz.Desc → DescTag
  | .bool => .bool
  | .uint _ => .uint
  | .byteVector _ => .byteVector
  | .byteList _ => .byteList
  | .bitVector _ => .bitVector
  | .bitList _ => .bitList
  | .progressiveBitList _ => .progressiveBitList
  | .vector _ _ => .vector
  | .list _ _ => .list
  | .progressiveList _ _ => .progressiveList
  | .container _ _ => .container
  | .progressiveContainer _ _ _ => .progressiveContainer
  | .compatibleUnion _ _ => .compatibleUnion

def erasedValueTag : Ssz.Value → ValueTag
  | .bool _ => .bool
  | .uint _ => .uint
  | .bytes _ => .bytes
  | .bits _ => .bits
  | .seq _ => .seq
  | .union _ _ => .union

def primitiveValueTag : Serialize.Value → ValueTag
  | .bool _ => .bool
  | .uint _ => .uint
  | .bytes _ => .bytes
  | .bits _ => .bits
  | .seq _ => .seq
  | .union _ _ => .union

mutual

/-- Total erasure of raw borrowed declarations; even invalid SSZ schemas erase. -/
def Desc.erase : Desc → Ssz.Desc
  | .primitive shape => shape.erase
  | .vector element length => .vector element.erase length.value
  | .list element limit => .list element.erase limit.value
  | .progressiveList element limit =>
      .progressiveList element.erase (limit.map NatOperand.value)
  | .container fields => .container (fields.map Prod.fst) (Desc.eraseFields fields)
  | .progressiveContainer active fields =>
      .progressiveContainer active (fields.map Prod.fst) (Desc.eraseFields fields)
  | .compatibleUnion variants =>
      .compatibleUnion (variants.map (fun variant => variant.1.value))
        (Desc.eraseVariants variants)

/-- Field types in their original order; names are projected from the same pairs. -/
def Desc.eraseFields : List (String × Desc) → List Ssz.Desc
  | [] => []
  | (_, shape) :: rest => shape.erase :: Desc.eraseFields rest

/-- Option types in their original order, without validating selector values. -/
def Desc.eraseVariants : List (NatOperand × Desc) → List Ssz.Desc
  | [] => []
  | (_, shape) :: rest => shape.erase :: Desc.eraseVariants rest

end

mutual

def Value.erase : Value → Ssz.Value
  | .bool value => .bool value
  | .uint number => .uint number.value
  | .bytes data => .bytes data
  | .bits data => .bits (Ssz.unpackBits data.bytes data.count.toNat)
  | .seq values => .seq (Value.eraseList values)
  | .union selector value => .union selector.value value.erase

def Value.eraseList : List Value → List Ssz.Value
  | [] => []
  | value :: rest => value.erase :: Value.eraseList rest

end

/-- The existing primitive interface observes the exact native root payload.
Composite children are erased only in this adapter; their root tags still force
the existing primitive codec's wrong-kind branch. The recursive model itself
never stores these erased children. -/
def Value.toPrimitive : Value → Serialize.Value
  | .bool value => .bool value
  | .uint number => .uint number
  | .bytes data => .bytes data
  | .bits data => .bits data
  | .seq values => .seq (Value.eraseList values)
  | .union selector value => .union selector value.erase

/-- Immediate children, retaining order, duplicates, and original operands. -/
def Desc.children : Desc → List Desc
  | .primitive _ => []
  | .vector element _ | .list element _ | .progressiveList element _ => [element]
  | .container fields | .progressiveContainer _ fields => fields.map Prod.snd
  | .compatibleUnion variants => variants.map Prod.snd

def Value.children : Value → List Value
  | .seq values => values
  | .union _ value => [value]
  | _ => []

/-- Upstream type depth is a termination measure, never an admissibility bound. -/
def Desc.nesting (shape : Desc) : Nat := shape.erase.nesting

mutual

def Value.nesting : Value → Nat
  | .seq values => Value.deepestNesting values + 1
  | .union _ value => value.nesting + 1
  | _ => 1

def Value.deepestNesting : List Value → Nat
  | [] => 0
  | value :: rest => max value.nesting (Value.deepestNesting rest)

end

/- Physical slice-size conditions are optional representation conditions, not
semantic validity. They bound only the stored slice counts and UTF-8 byte counts
that must fit the shipped 64-bit hosts. They neither normalize NatOperand limbs
nor bound logical capacities, widths, selectors, nesting, or SSZ validity.
Address ranges, alignment, element strides, pointer provenance, immutable
sharing, and exclusion from writable storage belong to a later memory relation;
these predicates alone do not assert that any storage exists. -/

def operandSliceSized : NatOperand → Prop
  | .small _ => True
  | .large _ limbs => limbs.length < 2 ^ 64

def optionalOperandSliceSized : Option NatOperand → Prop
  | none => True
  | some operand => operandSliceSized operand

def primitiveSliceSized : Serialize.Desc → Prop
  | .bool => True
  | .uint operand | .byteVector operand | .byteList operand
  | .bitVector operand | .bitList operand => operandSliceSized operand
  | .progressiveBitList limit => optionalOperandSliceSized limit

mutual

def Desc.Physical : Desc → Prop
  | .primitive shape => primitiveSliceSized shape
  | .vector element length | .list element length =>
      element.Physical ∧ operandSliceSized length
  | .progressiveList element limit =>
      element.Physical ∧ optionalOperandSliceSized limit
  | .container fields => fields.length < 2 ^ 64 ∧ Desc.fieldsPhysical fields
  | .progressiveContainer active fields =>
      active.length < 2 ^ 64 ∧ fields.length < 2 ^ 64 ∧ Desc.fieldsPhysical fields
  | .compatibleUnion variants =>
      variants.length < 2 ^ 64 ∧ Desc.variantsPhysical variants

def Desc.fieldsPhysical : List (String × Desc) → Prop
  | [] => True
  | (name, shape) :: rest =>
      name.toUTF8.size < 2 ^ 64 ∧ shape.Physical ∧ Desc.fieldsPhysical rest

def Desc.variantsPhysical : List (NatOperand × Desc) → Prop
  | [] => True
  | (selector, shape) :: rest =>
      operandSliceSized selector ∧ shape.Physical ∧ Desc.variantsPhysical rest

end

mutual

def Value.Physical : Value → Prop
  | .bool _ => True
  | .uint number => operandSliceSized number
  | .bytes data => data.size < 2 ^ 64
  | .bits data => data.bytes.size < 2 ^ 64
  | .seq values => values.length < 2 ^ 64 ∧ Value.listPhysical values
  | .union selector value => operandSliceSized selector ∧ value.Physical

def Value.listPhysical : List Value → Prop
  | [] => True
  | value :: rest => value.Physical ∧ Value.listPhysical rest

end

end SszNative.Codec

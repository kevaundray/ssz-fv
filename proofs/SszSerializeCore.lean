import SszSerializeArena
import SszNatArithmetic
import SszDelimited
import SszPackedBits

set_option autoImplicit false

namespace SszNative.Serialize

/- This is the logical target for a native/ISA refinement, not an assembly proof.
It models borrowed representations, ordered helper calls and abstract byte writes.
It does not assign Rust ABI offsets or assert pointer provenance. Read-only inputs
may alias one another and already-used arena storage; an ISA memory contract must
exclude their overlap with the actual writable free suffix, output, and headers. -/

inductive Desc where
  | bool
  | uint (width : NatOperand)
  | byteVector (length : NatOperand)
  | byteList (limit : NatOperand)
  | bitVector (length : NatOperand)
  | bitList (limit : NatOperand)
  | progressiveBitList (limit : Option NatOperand)

/-- A native `Bits` value already obeys the representation invariant established
by its public constructor. Padding is unrestricted; no canonicality or successful
SSZ parsing is assumed. Its 128-bit count is physical representation, not a cap. -/
structure Packed where
  bytes : Ssz.Bytes
  count : BitVec 128
  sized : bytes.size = (count.toNat + 7) / 8

inductive Value where
  | bool (value : Bool)
  | uint (number : NatOperand)
  | bytes (data : Ssz.Bytes)
  | bits (data : Packed)
  | seq (values : List Ssz.Value)
  | union (selector : NatOperand) (value : Ssz.Value)

def Desc.erase : Desc → Ssz.Desc
  | .bool => .bool
  | .uint width => .uint width.value
  | .byteVector length => .byteVector length.value
  | .byteList limit => .byteList limit.value
  | .bitVector length => .bitVector length.value
  | .bitList limit => .bitList limit.value
  | .progressiveBitList limit => .progressiveBitList (limit.map NatOperand.value)

def Value.erase : Value → Ssz.Value
  | .bool value => .bool value
  | .uint number => .uint number.value
  | .bytes data => .bytes data
  | .bits data => .bits (Ssz.unpackBits data.bytes data.count.toNat)
  | .seq values => .seq values
  | .union selector value => .union selector.value value

/-- Slice lengths are physical. There is deliberately no restriction on logical
NatOperand widths, values, or optional capacities, including noncanonical limbs. -/
def Value.Physical : Value → Prop
  | .bytes data => data.size < 2 ^ 64
  | .bits data => data.bytes.size < 2 ^ 64
  | _ => True

inductive Error where
  | wrongType
  | scope (expected actual : NatOperand)
  | limit (expected actual : NatOperand)
  | arithmetic (reason : NatArithmetic.Failure)
  | outputTooSmall

inductive Host where
  | arithmetic (reason : NatArithmetic.Failure)
  | outputTooSmall
  deriving DecidableEq, Repr

def eraseResult {α : Type} : Except Error α → Except Host (Except Ssz.Err α)
  | .ok value => .ok (.ok value)
  | .error .wrongType => .ok (.error .typeMismatch)
  | .error (.scope expected actual) => .ok (.error (.scope expected.value actual.value))
  | .error (.limit expected actual) => .ok (.error (.overLimit expected.value actual.value))
  | .error (.arithmetic reason) => .error (.arithmetic reason)
  | .error .outputTooSmall => .error .outputTooSmall

/-- The ordered calls retain successful and failed attempts, the original result
representation, exact reservation, and written limbs. They are not rolled back. -/
structure Outcome (α : Type) where
  result : Except Error α
  used : Nat
  calls : List (NatArithmetic.Outcome NatOperand)

def unchanged {α : Type} (used : Nat) (result : Except Error α) : Outcome α :=
  ⟨result, used, []⟩

def bind {α β : Type} (first : Outcome α) (next : α → Nat → Outcome β) : Outcome β :=
  match first.result with
  | .error reason => ⟨.error reason, first.used, first.calls⟩
  | .ok value =>
    let second := next value first.used
    ⟨second.result, second.used, first.calls ++ second.calls⟩

/-- The existing shared native helper, without changing its allocation policy. -/
def fromWide (arena : Delimited.ArenaState) (wide : BitVec 128) : Outcome NatOperand :=
  let result := NatArithmetic.fromWide arena.base arena.capacity arena.used wide
  ⟨result.result.mapError Error.arithmetic, result.used, [result]⟩

def count (size : Nat) : NatOperand := .small (BitVec.ofNat 64 size)

def bitLength (number : Nat) : Nat := if number = 0 then 0 else number.log2 + 1

def requiredBytes (number : Nat) : Nat :=
  bitLength number / 8 + if bitLength number % 8 = 0 then 0 else 1

/-- A normalized logical specification of native bit_len's byte-width comparison.
The original operands remain intact; no normalization allocation is performed. -/
def uintFits (width number : NatOperand) : Prop := requiredBytes number.value ≤ width.value

instance (width number : NatOperand) : Decidable (uintFits width number) := by
  unfold uintFits
  infer_instance

def bounded (limit : Option NatOperand) (actual : NatOperand) (used : Nat) : Outcome Unit :=
  match limit with
  | none => unchanged used (.ok ())
  | some cap =>
    if actual.value ≤ cap.value then unchanged used (.ok ())
    else unchanged used (.error (.limit cap actual))

/-- Count construction precedes even an absent bound; encoded-width construction
occurs only after the bound passes, with the first helper's committed cursor. -/
def measureList (limit : Option NatOperand) (data : Packed)
    (arena : Delimited.ArenaState) : Outcome NatOperand :=
  bind (fromWide arena data.count) fun actual used =>
    bind (bounded limit actual used) fun _ used =>
      fromWide { arena with used := used } (BitVec.ofNat 128 (data.count.toNat / 8 + 1))

/-- All primitive leaves ignore retain: unlike composites they allocate no Plan
arrays. Error payload construction can itself exhaust scratch before semantic
rejection; later failure keeps every prior successful helper allocation. -/
def measure (desc : Desc) (value : Value) (arena : Delimited.ArenaState) : Outcome NatOperand :=
  match desc, value with
  | .bool, .bool _ => unchanged arena.used (.ok (count 1))
  | .uint width, .uint number =>
    if uintFits width number then unchanged arena.used (.ok width)
    else unchanged arena.used (.error .wrongType)
  | .byteVector length, .bytes bytes =>
    if length.value = bytes.size then unchanged arena.used (.ok (count bytes.size))
    else unchanged arena.used (.error (.scope length (count bytes.size)))
  | .byteList limit, .bytes bytes =>
    bind (bounded (some limit) (count bytes.size) arena.used) fun _ used =>
      unchanged used (.ok (count bytes.size))
  | .bitVector length, .bits bits =>
    if length.value = bits.count.toNat then unchanged arena.used (.ok (count bits.bytes.size))
    else bind (fromWide arena bits.count) fun actual used =>
      unchanged used (.error (.scope length actual))
  | .bitList limit, .bits bits => measureList (some limit) bits arena
  | .progressiveBitList limit, .bits bits => measureList limit bits arena
  | _, _ => unchanged arena.used (.error .wrongType)

/-- `to_usize` checks represented value, not physical limb count or padding. -/
def hostSize (size : NatOperand) (used : Nat) : Outcome Nat :=
  if size.value < 2 ^ 64 then unchanged used (.ok size.value)
  else unchanged used (.error .outputTooSmall)

def encodedSize (desc : Desc) (value : Value) (arena : Delimited.ArenaState) : Outcome Nat :=
  bind (measure desc value arena) hostSize

/-- Full-byte copies are abstracted as byte values to write, never output reads.
The existing limb extraction and packed-bit models describe the native loops,
memcpy prefixes, masked partial byte, and mandatory list delimiter byte. -/
def emit (desc : Desc) (value : Value) : Ssz.Bytes :=
  match desc, value with
  | .bool, .bool value => #[if value then 1 else 0]
  | .uint width, .uint number => Limbs.bytes number.words width.value
  | .byteVector _, .bytes bytes | .byteList _, .bytes bytes => bytes
  | .bitVector _, .bits bits => PackedBits.canonicalBytes bits.bytes bits.count.toNat
  | .bitList _, .bits bits | .progressiveBitList _, .bits bits =>
    PackedBits.delimitedBytes bits.bytes bits.count.toNat
  | _, _ => #[]

/-- Only successful emission carries writes. Every pre-emit error has the empty
write list, including errors after committed count construction. -/
structure Written where
  outcome : Outcome Nat
  writes : Ssz.Bytes

def serialize (desc : Desc) (value : Value) (capacity : Nat)
    (arena : Delimited.ArenaState) : Written :=
  let sized := encodedSize desc value arena
  match sized.result with
  | .error _ => ⟨sized, #[]⟩
  | .ok size =>
    if size ≤ capacity then ⟨sized, emit desc value⟩
    else ⟨⟨.error .outputTooSmall, sized.used, sized.calls⟩, #[]⟩

structure Allocated where
  outcome : Outcome Nat
  reservation : Option Arena.Reservation
  writes : Ssz.Bytes

/-- measure → host_size → byte reservation → emit. MaybeUninit initialization
before emit does not read or initialize an output byte. A failed reservation
leaves the already committed measurement cursor and writes intact. -/
def serializeAlloc (desc : Desc) (value : Value) (arena : Delimited.ArenaState) : Allocated :=
  let sized := encodedSize desc value arena
  match sized.result with
  | .error _ => ⟨sized, none, #[]⟩
  | .ok size =>
    match Arena.reserveBytes arena.base arena.capacity sized.used size with
    | none => ⟨⟨.error (.arithmetic .scratchExhausted), sized.used, sized.calls⟩, none, #[]⟩
    | some reservation =>
      ⟨⟨.ok size, reservation.used, sized.calls⟩, some reservation, emit desc value⟩

/-- An uninitialized output is an arbitrary Option-valued memory. Applying a
write prefix reads no old byte in that prefix; the untouched tail is framed. -/
def applyWrites (before : Nat → Option UInt8) (writes : Ssz.Bytes) : Nat → Option UInt8 :=
  fun index => if index < writes.size then writes[index]? else before index

end SszNative.Serialize

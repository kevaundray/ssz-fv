import SszCodecError
import SszCodecTypesProofs
import SszTypedArena
import SszFixedSize
import SszWordDecode
import SszBitVector
import SszDelimitedProofs

set_option autoImplicit false

namespace SszNative.CodecDecode

open Codec (Desc Value Error)

/-- Offsets are relative to the caller's original input, including under nesting.
The byte array is the mathematical content of a borrowed slice, not a copy effect. -/
structure Input where
  offset : Nat
  bytes : Ssz.Bytes

def Input.slice (input : Input) (start ending : Nat) : Input :=
  ⟨input.offset + start, input.bytes.extract start ending⟩

/-- Materialized native storage choices. Empty static sequences have no reservation;
zero-length arena reservations, when actually requested, remain present. -/
inductive Node where
  | bool (value : Bool)
  | uint (number : NatOperand)
  | bytes (offset : Nat) (data : Ssz.Bytes)
  | bits (offset : Nat) (data : Serialize.Packed)
  | seq (allocation : Option Arena.Reservation) (children : List Node)
  | union (selector : NatOperand) (allocation : Arena.Reservation) (child : Node)

mutual
  def Node.value : Node → Value
    | .bool value => .bool value
    | .uint number => .uint number
    | .bytes _ data => .bytes data
    | .bits _ data => .bits data
    | .seq _ children => .seq (Node.values children)
    | .union selector _ child => .union selector child.value

  def Node.values : List Node → List Value
    | [] => []
    | child :: children => child.value :: Node.values children
end

/-- Sizes/alignment observed on both native targets, not field-offset or ISA proofs. -/
def valueLayout : TypedArena.Layout := ⟨48, 4⟩
def slotLayout : TypedArena.Layout := ⟨40, 3⟩

structure Slot where
  width : Option NatOperand
  start : Nat
  ending : Nat

/-- Ordered helper attempts and logical initialized fields. Padding is unspecified. -/
inductive Effect where
  | fixedSize (desc : Desc) (arena : Delimited.ArenaState)
      (call : Serialize.Outcome (Option NatOperand))
  | add (left right : NatOperand) (arena : Delimited.ArenaState)
      (call : NatArithmetic.Outcome NatOperand)
  | mul (left right : NatOperand) (arena : Delimited.ArenaState)
      (call : NatArithmetic.Outcome NatOperand)
  | uint (input : Input) (arena : Delimited.ArenaState)
      (significant : Nat) (allocation : Option Arena.Reservation) (words : List (BitVec 64))
  | bitVector (length : NatOperand) (input : Input) (arena : Delimited.ArenaState)
      (call : BitVector.Outcome)
  | delimited (limit : Option NatOperand) (input : Input) (arena : Delimited.ArenaState)
      (call : Delimited.Outcome)
  | reserve (layout : TypedArena.Layout) (count : Nat) (arena : Delimited.ArenaState)
      (allocation : Option Arena.Reservation)
  | writeSlot (address index : Nat) (slot : Slot)
  | writeValue (address index : Nat) (node : Node)

structure Outcome (α : Type) where
  result : Except Error α
  used : Nat
  effects : List Effect

def unchanged {α : Type} (used : Nat) (result : Except Error α) : Outcome α :=
  ⟨result, used, []⟩

def bind {α β : Type} (first : Outcome α) (next : α → Nat → Outcome β) : Outcome β :=
  match first.result with
  | .error reason => ⟨.error reason, first.used, first.effects⟩
  | .ok value =>
    let second := next value first.used
    ⟨second.result, second.used, first.effects ++ second.effects⟩

def scratch : Error := .primitive (.arithmetic .scratchExhausted)
def representation : Error := .primitive (.arithmetic .badRepresentation)

def reserve (layout : TypedArena.Layout) (count : Nat) (arena : Delimited.ArenaState) :
    Outcome Arena.Reservation :=
  let allocation := TypedArena.reserve layout arena.base arena.capacity arena.used count
  match allocation with
  | none => ⟨.error scratch, arena.used, [.reserve layout count arena none]⟩
  | some allocated => ⟨.ok allocated, allocated.used,
      [.reserve layout count arena (some allocated)]⟩

def exact (expected : NatOperand) (actual used : Nat) : Outcome Unit :=
  if expected.value = actual then unchanged used (.ok ())
  else unchanged used (.error (.primitive (.scope expected (Serialize.count actual))))

def bounded (limit : Option NatOperand) (actual : NatOperand) (used : Nat) : Outcome Unit :=
  let call := Serialize.bounded limit actual used
  ⟨call.result.mapError Error.primitive, call.used, []⟩

def compositeSize (size used : Nat) : Outcome Unit :=
  if 2 ^ 32 ≤ size then unchanged used (.error (.offsetOverflow (Serialize.count size)))
  else unchanged used (.ok ())

def narrow (number : NatOperand) (failure : Error) (used : Nat) : Outcome Nat :=
  if number.value < 2 ^ 64 then unchanged used (.ok number.value)
  else unchanged used (.error failure)

def fixedSize (desc : Desc) (arena : Delimited.ArenaState) : Outcome (Option NatOperand) :=
  let call := FixedSize.fixedSize desc arena
  ⟨call.result.mapError Error.primitive, call.used, [.fixedSize desc arena call]⟩

def add (left right : NatOperand) (arena : Delimited.ArenaState) : Outcome NatOperand :=
  let call := NatAdd.run left right arena.base arena.capacity arena.used
  ⟨call.result.mapError (fun reason => .primitive (.arithmetic reason)), call.used,
    [.add left right arena call]⟩

def mul (left right : NatOperand) (arena : Delimited.ArenaState) : Outcome NatOperand :=
  let call := NatMul.run left right arena.base arena.capacity arena.used
  ⟨call.result.mapError (fun reason => .primitive (.arithmetic reason)), call.used,
    [.mul left right arena call]⟩

def writeSlot (allocation : Arena.Reservation) (index : Nat) (slot : Slot)
    (used : Nat) : Outcome Unit :=
  ⟨.ok (), used, [.writeSlot (allocation.pointer + slotLayout.size * index) index slot]⟩

def writeValue (allocation : Arena.Reservation) (index : Nat) (node : Node)
    (used : Nat) : Outcome Unit :=
  ⟨.ok (), used, [.writeValue (allocation.pointer + valueLayout.size * index) index node]⟩

/-- The native high-zero scan precedes the small/large decision. Only significant
bytes are packed, and failed reservations record no initialized words. -/
def unsigned (input : Input) (arena : Delimited.ArenaState) : Outcome Node :=
  let significant := WordDecode.significantBytes input.bytes input.bytes.size
  if significant ≤ 8 then
    ⟨.ok (.uint (.small (WordDecode.packPrefix input.bytes 0 significant))), arena.used,
      [.uint input arena significant none []]⟩
  else
    match Arena.reserve arena.base arena.capacity arena.used ((significant + 7) / 8) with
    | none => ⟨.error scratch, arena.used, [.uint input arena significant none []]⟩
    | some allocation =>
      let words := WordDecode.decodeWords input.bytes 0 significant
      ⟨.ok (.uint (.large (BitVec.ofNat 64 allocation.pointer) words)), allocation.used,
        [.uint input arena significant (some allocation) words]⟩

def bitVectorError : BitVector.Error → Error
  | .arithmetic reason => .primitive (.arithmetic reason)
  | .scope expected actual => .primitive (.scope expected (Serialize.count actual))
  | .paddingBits => .paddingBits

/-- Bits::new's exact byte-count check remains explicit. -/
def packed (offset : Nat) (bytes : Ssz.Bytes) (count : BitVec 128) (used : Nat) : Outcome Node :=
  if sized : bytes.size = (count.toNat + 7) / 8 then
    unchanged used (.ok (.bits offset ⟨bytes, count, sized⟩))
  else unchanged used (.error representation)

def bitVector (length : NatOperand) (input : Input) (arena : Delimited.ArenaState) :
    Outcome Node :=
  let call := BitVector.run length input.bytes arena
  bind ⟨call.result.mapError bitVectorError, call.used, [.bitVector length input arena call]⟩
    fun count used => packed input.offset input.bytes count used

/-- Native count representation retained on a failed bound check. -/
def preparedNumber (ready : Delimited.Prepared) : NatOperand :=
  match ready.allocation with
  | none => .small ready.count.low
  | some allocation => .large (BitVec.ofNat 64 allocation.pointer)
      [ready.count.low, ready.count.high]

/-- The same scan/count/reservation algorithm as Delimited.run, with the original
native limit and allocated actual-count operand kept at the error boundary. -/
def delimited (limit : Option NatOperand) (input : Input) (arena : Delimited.ArenaState) :
    Outcome Node :=
  let call := Delimited.run (limit.map NatOperand.value) input.bytes arena
  let finish : Outcome Node :=
    if input.bytes.size = 0 then unchanged arena.used (.error .emptyEncoding)
    else
      let finalByte := input.bytes[input.bytes.size - 1]!
      if finalByte = 0 then
        unchanged arena.used (.error (if Delimited.scanZeros input.bytes then
          .noDelimiter else .trailingZeros))
      else
        let highest := Ssz.highestBit finalByte
        match Delimited.prepare arena (Delimited.countWords input.bytes.size highest) with
        | none => unchanged arena.used (.error scratch)
        | some ready =>
          bind (bounded limit (preparedNumber ready) ready.used) fun _ used =>
            let bytes := input.bytes.extract 0 (Delimited.retainedBytes input.bytes.size highest)
            packed input.offset bytes (BitVec.ofNat 128 ready.count.value) used
  ⟨finish.result, finish.used, [.delimited limit input arena call]⟩

def primitive (shape : Serialize.Desc) (input : Input) (arena : Delimited.ArenaState) :
    Outcome Node :=
  match shape with
  | .bool =>
    bind (exact (.small 1) input.bytes.size arena.used) fun _ used =>
      let byte := input.bytes[0]!
      if byte = 0 then unchanged used (.ok (.bool false))
      else if byte = 1 then unchanged used (.ok (.bool true))
      else unchanged used (.error (.notABit (.small (BitVec.ofNat 64 byte.toNat))))
  | .uint width =>
    bind (exact width input.bytes.size arena.used) fun _ used =>
      unsigned input { arena with used := used }
  | .byteVector length =>
    bind (exact length input.bytes.size arena.used) fun _ used =>
      unchanged used (.ok (.bytes input.offset input.bytes))
  | .byteList limit =>
    bind (bounded (some limit) (Serialize.count input.bytes.size) arena.used) fun _ used =>
      unchanged used (.ok (.bytes input.offset input.bytes))
  | .bitVector length => bitVector length input arena
  | .bitList limit => delimited (some limit) input arena
  | .progressiveBitList limit => delimited limit input arena

end SszNative.CodecDecode

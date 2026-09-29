import SszArm.CodecStorageBase

namespace SszArm.Codec.Storage

open SszNative (NatOperand)
open SszNative.Codec (Desc Value)
open Delimited (Span Protected MemoryFrame)

/-- The seven primitive payloads reuse the established Nat representation. -/
def primitive (address : Nat) (shape : SszNative.Serialize.Desc) : Image :=
  .word address 8 (Emit.descriptorTag shape).toNat ⋏
  match shape with
  | .bool => .pure True
  | .uint n | .byteVector n | .byteList n | .bitVector n | .bitList n =>
      .operand (address + 8) n
  | .progressiveBitList limit => optionOperand (address + 8) limit

def utf8 (address : Nat) (name : String) : Image :=
  .existsPointer fun pointer =>
    .word address 8 pointer ⋏ .word (address + 8) 8 name.toUTF8.size ⋏
    slice pointer name.toUTF8.size 1 1 ⋏
    entries (fun a (byte : UInt8) => .word a 1 byte.toNat) 1 pointer name.toUTF8.data.toList

def activeBits (address : Nat) (active : List Bool) : Image :=
  .existsPointer fun pointer =>
    .word address 8 pointer ⋏ .word (address + 8) 8 active.length ⋏
    slice pointer active.length 1 1 ⋏
    entries (fun a flag => .word a 1 (if flag then 1 else 0)) 1 pointer active

mutual
  def desc (address : Nat) : Desc → Image
    | .primitive shape => record address 40 8 (primitive address shape)
    | .vector element length => record address 40 8 (
        .word address 8 7 ⋏ .operand (address + 8) length ⋏
        .existsPointer fun pointer => .word (address + 24) 8 pointer ⋏ desc pointer element)
    | .list element limit => record address 40 8 (
        .word address 8 8 ⋏ .operand (address + 8) limit ⋏
        .existsPointer fun pointer => .word (address + 24) 8 pointer ⋏ desc pointer element)
    | .progressiveList element limit => record address 40 8 (
        .word address 8 9 ⋏ optionOperand (address + 16) limit ⋏
        .existsPointer fun pointer => .word (address + 8) 8 pointer ⋏ desc pointer element)
    | .container fields => record address 40 8 (
        .word address 8 10 ⋏ .existsPointer fun pointer =>
        .word (address + 8) 8 pointer ⋏ .word (address + 16) 8 fields.length ⋏
        slice pointer fields.length 24 8 ⋏ fieldEntries pointer fields)
    | .progressiveContainer active fields => record address 40 8 (
        .word address 8 11 ⋏ activeBits (address + 8) active ⋏
        .existsPointer fun pointer =>
        .word (address + 24) 8 pointer ⋏ .word (address + 32) 8 fields.length ⋏
        slice pointer fields.length 24 8 ⋏ fieldEntries pointer fields)
    | .compatibleUnion variants => record address 40 8 (
        .word address 8 12 ⋏ .existsPointer fun pointer =>
        .word (address + 8) 8 pointer ⋏ .word (address + 16) 8 variants.length ⋏
        slice pointer variants.length 24 8 ⋏ variantEntries pointer variants)

  def fieldEntries (address : Nat) : List (String × Desc) → Image
    | [] => .pure True
    | (name, shape) :: rest =>
        record address 24 8 (utf8 address name ⋏ .existsPointer fun pointer =>
          .word (address + 16) 8 pointer ⋏ desc pointer shape) ⋏
        fieldEntries (address + 24) rest

  def variantEntries (address : Nat) : List (NatOperand × Desc) → Image
    | [] => .pure True
    | (selector, shape) :: rest =>
        record address 24 8 (.operand (address + 8) selector ⋏ .existsPointer fun pointer =>
          .word address 8 pointer ⋏ desc pointer shape) ⋏
        variantEntries (address + 24) rest
end

/-- Byte and bit backings retain the actual observed pointer, not a fresh copy. -/
def bytesValue (address pointerOffset : Nat) (data : Ssz.Bytes) : Image :=
  .existsPointer fun pointer =>
    .word (address + pointerOffset) 8 pointer ⋏
    .word (address + pointerOffset + 8) 8 data.size ⋏
    slice pointer data.size 1 1 ⋏ .bytes pointer data

mutual
  def value (address : Nat) : Value → Image
    | .bool flag => record address 48 16 (
        .word address 1 0 ⋏ .word (address + 1) 1 (if flag then 1 else 0))
    | .uint number => record address 48 16 (
        .word address 1 1 ⋏ .operand (address + 8) number)
    | .bytes data => record address 48 16 (
        .word address 1 2 ⋏ bytesValue address 8 data)
    | .bits data => record address 48 16 (
        .word address 1 3 ⋏ bytesValue address 16 data.bytes ⋏
        .word (address + 32) 8 (data.count.setWidth 64).toNat ⋏
        .word (address + 40) 8 ((data.count >>> 64).setWidth 64).toNat)
    | .seq children => record address 48 16 (
        .word address 1 4 ⋏ .existsPointer fun pointer =>
        .word (address + 8) 8 pointer ⋏ .word (address + 16) 8 children.length ⋏
        slice pointer children.length 48 16 ⋏ valueEntries pointer children)
    | .union selector child => record address 48 16 (
        .word address 1 5 ⋏ .operand (address + 8) selector ⋏
        .existsPointer fun pointer => .word (address + 24) 8 pointer ⋏ value pointer child)

  def valueEntries (address : Nat) : List Value → Image
    | [] => .pure True
    | child :: rest => value address child ⋏ valueEntries (address + 48) rest
end

def DescAt (s : ArmState) (address : Nat) (shape : Desc) : Prop :=
  (desc address shape).At s

def DescOwned (writes : List Span) (s : ArmState) (address : Nat) (shape : Desc) : Prop :=
  (desc address shape).Owned writes s

def ValueAt (s : ArmState) (address : Nat) (logical : Value) : Prop :=
  (value address logical).At s

def ValueOwned (writes : List Span) (s : ArmState) (address : Nat) (logical : Value) : Prop :=
  (value address logical).Owned writes s

theorem desc_at {writes s address shape} (input : DescOwned writes s address shape) :
    DescAt s address shape := input.at

theorem value_at {writes s address logical} (input : ValueOwned writes s address logical) :
    ValueAt s address logical := input.at

theorem desc_preserved {writes s t address shape} (input : DescOwned writes s address shape)
    (frame : MemoryFrame writes s t) : DescOwned writes t address shape :=
  Image.preserved _ frame input

theorem value_preserved {writes s t address logical} (input : ValueOwned writes s address logical)
    (frame : MemoryFrame writes s t) : ValueOwned writes t address logical :=
  Image.preserved _ frame input

end SszArm.Codec.Storage

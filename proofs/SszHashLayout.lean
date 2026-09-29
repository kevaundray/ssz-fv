import SszHashLayoutArithmetic
import SszHashLayoutPacked
import SszHashLayoutNested

set_option autoImplicit false

namespace SszNative.HashLayout

open Codec (Desc Value)

/-- Borrowed logical views, never a serialized buffer or an array of child roots. -/
inductive Leaves where
  | packed (view : Packed)
  | nested (view : Nested)

structure Layout where
  leaves : Leaves
  limit : Option NatOperand
  mixin : Option Ssz.Bytes

def Layout.count (view : Layout) : Nat :=
  match view.leaves with
  | .packed packed => packed.count
  | .nested nested => nested.count

def Layout.isPacked (view : Layout) : Bool :=
  match view.leaves with
  | .packed _ => true
  | .nested _ => false

def Layout.nested (view : Layout) (index : Nat) : Option (Desc × Value) :=
  match view.leaves with
  | .packed _ => none
  | .nested nested => nested.at index

/-- All scalar checks finish before the first multiplication or division attempt. -/
def sequence (element : Desc) (values : List Value) (positions : Option NatOperand)
    (mixin : Option Ssz.Bytes) (arena : Delimited.ArenaState) : Outcome Layout :=
  bind (lift arena.used (basicWidth element)) fun width used =>
    match width with
    | none => unchanged used (.ok ⟨.nested (.sequence element values), positions, mixin⟩)
    | some width =>
      bind (lift used (checkScalars element values)) fun _ used =>
        match positions with
        | none => unchanged used (.ok ⟨.packed (.basic values width), none, mixin⟩)
        | some count =>
          bind (mul count (Serialize.count width) { arena with used := used }) fun bytes used =>
            bind (ceilDiv bytes 32 { arena with used := used }) fun limit used =>
              unchanged used (.ok ⟨.packed (.basic values width), some limit, mixin⟩)

/-- Source branch order, including allocation while constructing bit-count errors.
Logical limits, field metadata and raw NatOperand representations remain intact. -/
def layout (desc : Desc) (value : Value) (arena : Delimited.ArenaState) : Outcome Layout :=
  match desc, value with
  | .primitive .bool, _ | .primitive (.uint _), _ =>
      bind (lift arena.used (scalar desc value)) fun pair used =>
        unchanged used (.ok ⟨.packed (.scalar pair.1 pair.2),
          some (Serialize.count ((pair.2 + 31) / 32)), none⟩)
  | .primitive (.byteVector length), .bytes data =>
      if length.value = data.size then
        unchanged arena.used (.ok ⟨.packed (.bytes data),
          some (Serialize.count ((data.size + 31) / 32)), none⟩)
      else unchanged arena.used (.error (.codec (.primitive (.scope length (Serialize.count data.size)))))
  | .primitive (.byteList limit), .bytes data =>
      if limit.value < data.size then
        unchanged arena.used (.error (.codec (.primitive (.limit limit (Serialize.count data.size)))))
      else bind (ceilDiv limit 32 arena) fun capacity used =>
        unchanged used (.ok ⟨.packed (.bytes data), some capacity,
          some (countWord128 (BitVec.ofNat 128 data.size))⟩)
  | .primitive (.bitVector length), .bits data =>
      if length.value = data.count.toNat then
        bind (ceilDiv length 256 arena) fun capacity used =>
          unchanged used (.ok ⟨.packed (.bits data), some capacity, none⟩)
      else bind (fromWide data.count arena) fun actual used =>
        unchanged used (.error (.codec (.primitive (.scope length actual))))
  | .primitive (.bitList limit), .bits data =>
      if limit.value < data.count.toNat then
        bind (fromWide data.count arena) fun actual used =>
          unchanged used (.error (.codec (.primitive (.limit limit actual))))
      else bind (ceilDiv limit 256 arena) fun capacity used =>
        unchanged used (.ok ⟨.packed (.bits data), some capacity, some (countWord128 data.count)⟩)
  | .primitive (.progressiveBitList _), .bits data =>
      unchanged arena.used (.ok ⟨.packed (.bits data), none, some (countWord128 data.count)⟩)
  | .vector element length, .seq values =>
      if length.value = values.length then sequence element values (some length) none arena
      else unchanged arena.used (.error (.codec (.primitive (.scope length (Serialize.count values.length)))))
  | .list element limit, .seq values =>
      if limit.value < values.length then
        unchanged arena.used (.error (.codec (.primitive (.limit limit (Serialize.count values.length)))))
      else sequence element values (some limit)
        (some (countWord128 (BitVec.ofNat 128 values.length))) arena
  | .progressiveList element _, .seq values =>
      sequence element values none (some (countWord128 (BitVec.ofNat 128 values.length))) arena
  | .container fields, .seq values =>
      if fields.length = values.length then
        unchanged arena.used (.ok ⟨.nested (.fields fields values),
          some (Serialize.count fields.length), none⟩)
      else unchanged arena.used (.error wrongType)
  | .progressiveContainer active fields, .seq values =>
      if fields.length = values.length then
        let count := active.countP id
        if count = fields.length then
          unchanged arena.used (.ok ⟨.nested (.progressive active fields values),
            none, some (MerkleWords.activeFieldsWord active)⟩)
        else unchanged arena.used (.error (.layoutFieldCount
          (Serialize.count count) (Serialize.count fields.length)))
      else unchanged arena.used (.error wrongType)
  | .compatibleUnion options, .union selector value =>
      match lookup options selector with
      | none => unchanged arena.used (.error (.codec (.unknownSelector selector)))
      | some chosen =>
          if 255 < selector.value then
            unchanged arena.used (.error (.unionSelectorRange selector (.small 0) (.small 255)))
          else unchanged arena.used (.ok ⟨.nested (.union chosen value), some (.small 1),
            some (MerkleWords.lengthWord selector)⟩)
  | _, _ => unchanged arena.used (.error wrongType)

/-- Indexed leaf access receives a recursive visitor only for an actual selected
child. Out-of-range accesses and progressive gaps are allocation-free zero leaves. -/
def leafRoot (view : Layout) (index : Nat) (arena : Delimited.ArenaState)
    (visit : (desc : Desc) → (value : Value) →
      view.nested index = some (desc, value) → Delimited.ArenaState → Outcome Ssz.Bytes) :
    Outcome Ssz.Bytes :=
  if index < view.count then
    match packedEq : view.leaves with
    | .packed packed => lift arena.used (packedChunk packed index)
    | .nested nested =>
        match childEq : nested.at index with
        | none => unchanged arena.used (.ok Ssz.zeroChunk)
        | some (desc, value) =>
            visit desc value (by simp only [Layout.nested, packedEq, childEq]) arena
  else unchanged arena.used (.ok Ssz.zeroChunk)

end SszNative.HashLayout

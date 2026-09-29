import SszHashLayoutTypes

set_option autoImplicit false

namespace SszNative.HashLayout

open Codec (Desc Value)

inductive Packed where
  | bytes (data : Ssz.Bytes)
  | bits (data : Serialize.Packed)
  | scalar (number : NatOperand) (width : Nat)
  | basic (values : List Value) (width : Nat)

/-- The raw native width check precedes the value-fit check. -/
def scalar : Desc → Value → Except Error (NatOperand × Nat)
  | .primitive .bool, .bool bit => .ok (Serialize.count (if bit then 1 else 0), 1)
  | .primitive (.uint width), .uint number =>
      if width.value ≤ 32 then
        if Serialize.uintFits width number then .ok (number, width.value)
        else .error wrongType
      else .error (arithmeticError .badRepresentation)
  | _, _ => .error wrongType

def basicWidth : Desc → Except Error (Option Nat)
  | .primitive .bool => .ok (some 1)
  | .primitive (.uint width) =>
      if width.value ≤ 32 then .ok (some width.value)
      else .error (arithmeticError .badRepresentation)
  | _ => .ok none

/-- All values are checked, in source order, before any capacity arithmetic. -/
def checkScalars (desc : Desc) : List Value → Except Error Unit
  | [] => .ok ()
  | value :: rest => do
      let _ ← scalar desc value
      checkScalars desc rest

def Packed.byteCount : Packed → Nat
  | .bytes data => data.size
  | .bits data => data.bytes.size
  | .scalar _ width => width
  | .basic values width => values.length * width

def Packed.count (packed : Packed) : Nat := (packed.byteCount + 31) / 32

/-- The multiplication guard proves both a positive divisor and a valid slice
index; no division-by-zero or default-valued sequence read is executed. -/
theorem basic_index_bound (values : List Value) (width position : Nat)
    (inside : position < values.length * width) : position / width < values.length := by
  have positive : 0 < width := by
    cases width with
    | zero => simp at inside
    | succ width => exact Nat.zero_lt_succ width
  exact (Nat.div_lt_iff_lt_mul positive).mpr inside

/-- One native byte read. Only the final partial bit byte is masked. -/
def Packed.bytesAt : Packed → Nat → Except Error UInt8
  | .bytes data, position =>
      .ok (if inside : position < data.size then data[position] else 0)
  | .bits data, position =>
      .ok (if inside : position < data.bytes.size then
        if position = data.count.toNat / 8 ∧ data.count.toNat % 8 ≠ 0 then
          data.bytes[position] &&& UInt8.ofNat (2 ^ (data.count.toNat % 8) - 1)
        else data.bytes[position]
      else 0)
  | .scalar number width, position =>
      .ok (if position < width then Limbs.byteAt number.words position else 0)
  | .basic values width, position =>
      if inside : position < values.length * width then
        match values[position / width]'(basic_index_bound values width position inside) with
        | .bool bit => .ok (if bit then 1 else 0)
        | .uint number => .ok (Limbs.byteAt number.words (position % width))
        | _ => .error wrongType
      else .ok 0

/-- Completed iterations of the native fixed-size, zero-initialized chunk fill.
Every failed byte read stops before any later byte is inspected. -/
def fillPacked (packed : Packed) (start : Nat) : Nat → Except Error Ssz.Bytes
  | 0 => .ok (Array.replicate 32 0)
  | count + 1 => do
      let chunk ← fillPacked packed start count
      let byte ← packed.bytesAt (start + count)
      return chunk.set! count byte

/-- Layout handles its outer leaf-count guard; this helper fills one chunk. -/
def packedChunk (packed : Packed) (index : Nat) : Except Error Ssz.Bytes :=
  fillPacked packed (index * 32) 32

end SszNative.HashLayout

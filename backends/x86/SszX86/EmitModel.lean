import SszX86.EmitCore

namespace SszX86.Emit
open SszNative SszNative.Serialize

def descTag : Desc → Nat
  | .bool => 0 | .uint _ => 1 | .byteVector _ => 2 | .byteList _ => 3
  | .bitVector _ => 4 | .bitList _ => 5 | .progressiveBitList _ => 6

def valueTag : Value → Nat
  | .bool _ => 0 | .uint _ => 1 | .bytes _ => 2 | .bits _ => 3
  | .seq _ => 4 | .union _ _ => 5

/-- Logical type compatibility, derived from successful expectedSize. -/
def Compatible : Desc → Value → Prop
  | .bool, .bool _ | .uint _, .uint _ => True
  | .byteVector _, .bytes _ | .byteList _, .bytes _ => True
  | .bitVector _, .bits _ | .bitList _, .bits _ | .progressiveBitList _, .bits _ => True
  | _, _ => False

theorem success_compatible (desc : Desc) (value : Value) (size : Nat)
    (success : expectedSize desc value = .ok size) : Compatible desc value := by
  cases desc <;> cases value <;> simp_all [Compatible, expectedSize]

/-- Seq/Union table slots cannot be reached by a valid primitive call. -/
theorem success_value_tag (desc : Desc) (value : Value) (size : Nat)
    (success : expectedSize desc value = .ok size) : valueTag value < 4 := by
  have compatible := success_compatible desc value size success
  cases desc <;> cases value <;> simp_all [Compatible, valueTag]

structure ValidCall (desc : Desc) (value : Value) (capacity size : Nat) : Prop where
  success : expectedSize desc value = .ok size
  representable : size < 2 ^ 64
  fits : size ≤ capacity

theorem ValidCall.emitted_size {desc : Desc} {value : Value} {capacity size : Nat}
    (valid : ValidCall desc value capacity size) : (emit desc value).size = size :=
  (expected_encoding desc value).2 size valid.success

theorem ValidCall.pinned {desc : Desc} {value : Value} {capacity size : Nat}
    (valid : ValidCall desc value capacity size) :
    Ssz.serialize desc.erase value.erase = .ok (emit desc value) := by
  rw [(expected_encoding desc value).1, valid.success]
  rfl

end SszX86.Emit

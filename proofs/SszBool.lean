import SszNatMemory
import Ssz.Codec.Deserialize

set_option autoImplicit false

namespace SszNative.BoolCodec
open SszNative.NatMemory (smallAt)

/-- The boolean branch's complete result, including both rejection classes.
The byte observation is irrelevant when the input length is not one. -/
def outcome (length : Nat) (byte : UInt8) : Except Ssz.Err Ssz.Value :=
  if length = 1 then
    if byte = 0 then .ok (.bool false)
    else if byte = 1 then .ok (.bool true)
    else .error (.notABit byte.toNat)
  else .error (.scope 1 length)

theorem outcome_eq_deserialize (data : Ssz.Bytes) :
    outcome data.size data[0]! = Ssz.deserialize .bool data := by
  by_cases length : data.size = 1
  · simp [outcome, Ssz.deserialize, length]
    split <;> (try simp_all) <;> (try rfl)
    split <;> simp_all <;> rfl
  · simp [outcome, Ssz.deserialize, length] <;> rfl

/- The following predicates describe the pinned Rust compiler's INTERNAL
Result<Value, Error> storage, not the public C ABI. `load offset width` observes
an unsigned little-endian word relative to the result pointer, or none if absent.
All fields are taken from the actual boolean decoder instruction blocks.
Padding is intentionally unconstrained; machine theorems must provide frames. -/

def errorAt (load : Nat → Nat → Option Nat) (reason first second : Nat) : Prop :=
  load 0 8 = some 1 ∧
  load 8 8 = some 1 ∧
  load 16 8 = some 0 ∧
  smallAt load 24 first ∧
  smallAt load 40 second ∧
  smallAt load 56 0 ∧
  load 72 4 = some reason

def ResultAt (load : Nat → Nat → Option Nat) : Except Ssz.Err Ssz.Value → Prop
  | .ok (.bool value) =>
    load 0 8 = some 0 ∧ load 16 2 = some (if value then 256 else 0)
  | .error (.scope expected actual) => errorAt load 3 expected actual
  | .error (.notABit byte) => errorAt load 13 byte 0
  | _ => False

/-- Interpreting an observed native boolean result yields the pinned SSZ result. -/
theorem result_refines (data : Ssz.Bytes) (load : Nat → Nat → Option Nat)
    (observed : ResultAt load (outcome data.size data[0]!)) :
    ResultAt load (Ssz.deserialize .bool data) := by
  rwa [outcome_eq_deserialize] at observed

end SszNative.BoolCodec

import SszNatMemory
import SszWordDecode

set_option autoImplicit false

namespace SszNative.UintCodec

/-- Internal Result<Value, Error> fields, observed at absolute addresses.
Scope errors retain the original descriptor Nat, including borrowed Large limbs. -/
def errorAt (load : Nat → Nat → Option Nat)
    (out reason expected actual : Nat) : Prop :=
  load out 8 = some 1 ∧ load (out + 8) 8 = some 1 ∧ load (out + 16) 8 = some 0 ∧
  NatMemory.At load (out + 24) expected ∧ NatMemory.At load (out + 40) actual ∧
  NatMemory.At load (out + 56) 0 ∧ load (out + 72) 4 = some reason

/-- Integer codec observations; padding and unrelated memory are left to frames. -/
def ResultAt (load : Nat → Nat → Option Nat) (out : Nat) : Except Ssz.Err Ssz.Value → Prop
  | .ok (.uint value) =>
    load out 8 = some 0 ∧ load (out + 16) 1 = some 1 ∧ NatMemory.At load (out + 24) value
  | .error (.scope expected actual) => errorAt load out 3 expected actual
  | _ => False

/-- Caller-scratch exhaustion is a host resource error, not an upstream SSZ error.
Machine proofs must establish the failed reservation condition separately. -/
def scratchExhaustedAt (load : Nat → Nat → Option Nat) (out : Nat) : Prop :=
  errorAt load out 32768 0 0

theorem result_refines (width : Nat) (data : Ssz.Bytes)
    (load : Nat → Nat → Option Nat) (out : Nat)
    (observed : ResultAt load out (WordDecode.outcome width data)) :
    ResultAt load out (Ssz.deserialize (.uint width) data) := by
  rwa [WordDecode.outcome_eq_deserialize] at observed

end SszNative.UintCodec

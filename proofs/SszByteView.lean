import SszBytes
import SszUint

set_option autoImplicit false

namespace SszNative.ByteView

/-- Bytes borrowed from the original input, not a scratch allocation. -/
def BytesAt (load : Nat → Nat → Option Nat) (source : Nat) (data : Ssz.Bytes) : Prop :=
  ∀ i, i < data.size → load (source + i) 1 = some (data[i]?.getD 0).toNat

/-- Observe the internal Result<Value, Error>; padding belongs to the frame. -/
def ResultAt (load : Nat → Nat → Option Nat) (out : Nat) : Except Ssz.Err Ssz.Value → Prop
  | .ok (.bytes data) =>
    load out 8 = some 0 ∧ load (out + 16) 1 = some 2 ∧
      ∃ source, load (out + 24) 8 = some source ∧
        load (out + 32) 8 = some data.size ∧ BytesAt load source data
  | .error (.scope expected actual) => UintCodec.errorAt load out 3 expected actual
  | .error (.overLimit expected actual) => UintCodec.errorAt load out 2 expected actual
  | _ => False

def vectorOutcome (length : Nat) (data : Ssz.Bytes) : Except Ssz.Err Ssz.Value :=
  if data.size = length then .ok (.bytes data) else .error (.scope length data.size)

def listOutcome (limit : Nat) (data : Ssz.Bytes) : Except Ssz.Err Ssz.Value :=
  if data.size ≤ limit then .ok (.bytes data) else .error (.overLimit limit data.size)

theorem vector_outcome_eq_deserialize (length : Nat) (data : Ssz.Bytes) :
    vectorOutcome length data = Ssz.deserialize (.byteVector length) data := by
  by_cases h : data.size = length <;> simp [vectorOutcome, Ssz.deserialize, h] <;> rfl

theorem list_outcome_eq_deserialize (limit : Nat) (data : Ssz.Bytes) :
    listOutcome limit data = Ssz.deserialize (.byteList limit) data := by
  by_cases h : data.size ≤ limit
  · simp [listOutcome, Ssz.deserialize, h, Nat.not_lt.mpr h]; rfl
  · simp [listOutcome, Ssz.deserialize, h, Nat.lt_of_not_ge h]; rfl

end SszNative.ByteView

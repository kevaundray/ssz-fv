import SszBitVector

set_option autoImplicit false

namespace SszNative.BitVector

/-- Every written limb remains observable, including redundant high zeros. -/
def allocationAt {α : Type} (observe : Nat → Nat → Option Nat)
    (outcome : NatArithmetic.Outcome α) : Prop :=
  ∀ reservation, outcome.allocation = some reservation →
    NatMemory.wordsAt observe reservation.pointer outcome.written

/-- A later failure does not discard the first helper's memory effects. -/
def Outcome.writtenAt (outcome : Outcome) (observe : Nat → Nat → Option Nat) : Prop :=
  allocationAt observe outcome.divided ∧
    ∀ rounded, outcome.rounded = some rounded → allocationAt observe rounded

/-- Alignment padding is charged to the cursor but is not a written region. -/
def allocationWrites {α : Type} (outcome : NatArithmetic.Outcome α) : List (Nat × Nat) :=
  match outcome.allocation with
  | none => []
  | some reservation => [(reservation.pointer, 8 * outcome.written.length)]

def Outcome.writes (outcome : Outcome) : List (Nat × Nat) :=
  allocationWrites outcome.divided ++
    match outcome.rounded with
    | none => []
    | some rounded => allocationWrites rounded

def failureAt (observe : Nat → Nat → Option Nat) (out : Nat)
    (reason : NatArithmetic.Failure) : Prop :=
  UintCodec.errorAt observe out (match reason with
    | .scratchExhausted => 32768
    | .badRepresentation => 32770) 0 0

/-- Native output fields retain the original borrowed pointer even for zero
bytes. Scope retains the precise expected Nat pair, not just its numeric value.
The ordinary Result<Value, Error> layout differs from private helper results. -/
def ResultAt (observe : Nat → Nat → Option Nat) (out source : Nat) (data : Ssz.Bytes) :
    Except Error (BitVec 128) → Prop
  | .ok count =>
    observe out 8 = some 0 ∧ observe (out + 16) 1 = some 3 ∧
    observe (out + 32) 8 = some source ∧ observe (out + 40) 8 = some data.size ∧
    observe (out + 48) 8 = some (count.toNat % 2^64) ∧
    observe (out + 56) 8 = some (count.toNat / 2^64) ∧
    ByteView.BytesAt observe source data ∧ data.size = (count.toNat + 7) / 8
  | .error (.arithmetic reason) => failureAt observe out reason
  | .error (.scope expected actual) =>
    UintCodec.errorAt observe out 3 expected.value actual ∧
      NatArithmetic.operandAt observe (out + 24) expected
  | .error .paddingBits => UintCodec.errorAt observe out 15 0 0

/-- The native memory contract exposes the existing SSZ observation without
forgetting scratch failure or relying on a successful-execution hypothesis. -/
theorem ResultAt.erased (observe : Nat → Nat → Option Nat) (out source : Nat)
    (data : Ssz.Bytes) (result : Except Error (BitVec 128))
    (stored : ResultAt observe out source data result) :
    match eraseResult data result with
    | .ok value => BitView.ResultAt observe out value
    | .error reason => failureAt observe out reason := by
  cases result with
  | ok count =>
    rcases stored with ⟨tag, kind, pointer, size, low, high, bytes, scope⟩
    simp only [eraseResult, BitView.ResultAt, Packing.unpackBits_size]
    exact ⟨tag, kind, count.isLt, low, high,
      source, data, pointer, size, scope, bytes, rfl⟩
  | error reason =>
    cases reason with
    | arithmetic reason => exact stored
    | scope expected actual => exact stored.1
    | paddingBits => exact stored

end SszNative.BitVector

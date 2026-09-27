import SszBitView
import SszArena
import SszNatABI

set_option autoImplicit false

namespace SszNative.Delimited

/-- Physical arena metadata; logical SSZ capacities remain unrestricted Nats. -/
structure ArenaState where
  base : Nat
  capacity : Nat
  used : Nat
  deriving DecidableEq, Repr

/-- The implementation's two-word bit count, not an architectural register file. -/
structure CountWords where
  low : BitVec 64
  high : BitVec 64
  deriving DecidableEq, Repr

def CountWords.value (count : CountWords) : Nat :=
  count.low.toNat + 2^64 * count.high.toNat

/-- Called after the nonempty-input guard. Arithmetic is explicitly word-sized. -/
def countWords (length highest : Nat) : CountWords :=
  let preceding := BitVec.ofNat 64 (length - 1)
  ⟨preceding * 8#64 + BitVec.ofNat 64 highest, preceding >>> 61⟩

def retainedBytes (length highest : Nat) : Nat :=
  if highest = 0 then length - 1 else length

/-- The zero scan's logical cursor. Array.all uses the original array, not a copy. -/
def scanZeros (data : Ssz.Bytes) (index : Nat := 0) : Bool :=
  data.all (· == 0) index data.size

/-- Delimiter validation precedes count construction and any reservation. -/
def validate (data : Ssz.Bytes) : Except Ssz.Err UInt8 :=
  if data.size = 0 then .error .emptyEncoding
  else
    let finalByte := data[data.size - 1]!
    if finalByte = 0 then
      if scanZeros data then .error .noDelimiter else .error .trailingZeros
    else .ok finalByte

/-- A count ready for the bound check, including its committed storage choice. -/
structure Prepared where
  count : CountWords
  used : Nat
  allocation : Option Arena.Reservation
  deriving DecidableEq, Repr

def Prepared.pointer (ready : Prepared) : Nat :=
  match ready.allocation with
  | none => 0
  | some reservation => reservation.pointer

def Prepared.payload (ready : Prepared) : Nat :=
  match ready.allocation with
  | none => ready.count.low.toNat
  | some _ => 2

/-- None denotes exact reservation failure, not omission of the optional bound.
A large count is allocated even if no bound was supplied. -/
def prepare (arena : ArenaState) (count : CountWords) : Option Prepared :=
  if count.high = 0#64 then some ⟨count, arena.used, none⟩
  else
    match Arena.reserve arena.base arena.capacity arena.used 2 with
    | none => none
    | some reservation => some ⟨count, reservation.used, some reservation⟩

/-- A view into the original input; the native result does not copy these bytes. -/
structure Borrowed where
  offset : Nat
  bytes : Nat
  count : CountWords
  deriving DecidableEq, Repr

inductive Error where
  | semantic (reason : Ssz.Err)
  | scratchExhausted

/-- Keeping the prepared count on rejection specifies allocation-before-bound
checking and the exact actual-count representation copied into an error. Caller
limit representation is retained by the ISA memory relation, not canonicalized. -/
structure Outcome where
  result : Except Error Borrowed
  used : Nat
  prepared : Option Prepared

def Outcome.allocation (outcome : Outcome) : Option Arena.Reservation :=
  outcome.prepared.bind Prepared.allocation

/-- Exact contents of the count's newly reserved storage, even when no bound is
present and the representation is not copied to an error result. -/
def PreparedAt (observe : Nat → Nat → Option Nat) (ready : Prepared) : Prop :=
  match ready.allocation with
  | none => ready.count.high = 0#64
  | some reservation =>
    observe reservation.pointer 8 = some ready.count.low.toNat ∧
    observe (reservation.pointer + 8) 8 = some ready.count.high.toNat

def Outcome.PreparedAt (observe : Nat → Nat → Option Nat) (outcome : Outcome) : Prop :=
  ∀ ready, outcome.prepared = some ready → SszNative.Delimited.PreparedAt observe ready

/-- No reservation occurs in this phase. Both success and rejection retain it. -/
def finish (limit : Option Nat) (length highest : Nat) (ready : Prepared) : Outcome :=
  let result : Except Error Borrowed := match limit with
    | some cap =>
      if ready.count.value ≤ cap then
        .ok ⟨0, retainedBytes length highest, ready.count⟩
      else .error (.semantic (.overLimit cap ready.count.value))
    | none => .ok ⟨0, retainedBytes length highest, ready.count⟩
  ⟨result, ready.used, some ready⟩

/-- Native algorithm: validate → count → reserve/commit → bound → borrowed view.
No correctness assumption about this intermediate model is introduced. -/
def run (limit : Option Nat) (data : Ssz.Bytes) (arena : ArenaState) : Outcome :=
  match validate data with
  | .error reason => ⟨.error (.semantic reason), arena.used, none⟩
  | .ok finalByte =>
    let highest := Ssz.highestBit finalByte
    match prepare arena (countWords data.size highest) with
    | none => ⟨.error .scratchExhausted, arena.used, none⟩
    | some ready => finish limit data.size highest ready

/-- Erasure materializes the borrowed logical value only for comparison with SSZ.
A host-resource failure is not silently reclassified as an SSZ semantic error. -/
def Outcome.erase (outcome : Outcome) (data : Ssz.Bytes) : Option (Except Ssz.Err Ssz.Value) :=
  match outcome.result with
  | .error .scratchExhausted => none
  | .error (.semantic reason) => some (.error reason)
  | .ok view => some (.ok (.bits
      (Ssz.unpackBits (data.extract view.offset (view.offset + view.bytes)) view.count.value)))

/-- Nested guards avoid inspecting a nonexistent final byte of an empty input. -/
def NeedsAllocation (data : Ssz.Bytes) : Prop :=
  if data.size = 0 then False
  else if data[data.size - 1]! = 0 then False
  else 2^64 ≤ BitView.delimitedCount data

instance (data : Ssz.Bytes) : Decidable (NeedsAllocation data) := by
  unfold NeedsAllocation
  infer_instance

def Exhausted (data : Ssz.Bytes) (arena : ArenaState) : Prop :=
  NeedsAllocation data ∧ Arena.reserve arena.base arena.capacity arena.used 2 = none

instance (data : Ssz.Bytes) (arena : ArenaState) : Decidable (Exhausted data arena) := by
  unfold Exhausted
  infer_instance

def allocation (data : Ssz.Bytes) (arena : ArenaState) : Option Arena.Reservation :=
  if NeedsAllocation data then Arena.reserve arena.base arena.capacity arena.used 2 else none

/-- Exact output fields for the intermediate result. The caller's original
limit representation is copied verbatim on over-limit rejection. Architecture
proofs add their own stack/register/write frames around this shared relation. -/
def ResultAt (observe : Nat → Nat → Option Nat) (out source optionAddress : Nat)
    (data : Ssz.Bytes) (outcome : Outcome) : Prop :=
  match outcome.result with
  | .ok view =>
    observe out 8 = some 0 ∧ observe (out + 16) 1 = some 3 ∧
    observe (out + 32) 8 = some (source + view.offset) ∧
    observe (out + 40) 8 = some view.bytes ∧
    observe (out + 48) 8 = some view.count.low.toNat ∧
    observe (out + 56) 8 = some view.count.high.toNat ∧
    ByteView.BytesAt observe source data
  | .error .scratchExhausted => UintCodec.errorAt observe out 32768 0 0
  | .error (.semantic (.overLimit expected actual)) =>
    UintCodec.errorAt observe out 2 expected actual ∧
    observe (out + 24) 8 = observe (optionAddress + 8) 8 ∧
    observe (out + 32) 8 = observe (optionAddress + 16) 8 ∧
    ∃ ready, outcome.prepared = some ready ∧
      observe (out + 40) 8 = some ready.pointer ∧
      observe (out + 48) 8 = some ready.payload
  | .error (.semantic reason) => BitView.ResultAt observe out (.error reason)

end SszNative.Delimited

import SszIndicesTypes
import SszHashLayoutRoot
import SszHashStreamFinalize
import SszTypedArena
import Ssz.Merkle.Verify

set_option autoImplicit false

namespace SszNative.Proof

inductive CountReason where
  | count
  | branchLength
  | leafCount
  | proofLength
  deriving DecidableEq, Repr

def CountReason.erase (reason : CountReason) (expected actual : Nat) : Ssz.Err :=
  match reason with
  | .count => .count expected actual
  | .branchLength => .branchLength expected actual
  | .leafCount => .leafCount expected actual
  | .proofLength => .proofLength expected actual

inductive Error where
  | indices (reason : Indices.Error)
  | layout (reason : HashLayout.Error)
  | scratchExhausted
  | count (reason : CountReason) (expected actual : NatOperand)
  | pathIntoPacked
  | pathIntoGap
  | pathPastSpine
  | pathIntoMixin
  | proofIncomplete

def eraseResult {α : Type} : Except Error α → Except Serialize.Host (Except Ssz.Err α)
  | .ok value => .ok (.ok value)
  | .error (.indices reason) => Indices.eraseResult (.error reason)
  | .error (.layout reason) => HashLayout.eraseResult (.error reason)
  | .error .scratchExhausted => .error (.arithmetic .scratchExhausted)
  | .error (.count reason expected actual) => .ok (.error (reason.erase expected.value actual.value))
  | .error .pathIntoPacked => .ok (.error .pathIntoPacked)
  | .error .pathIntoGap => .ok (.error .pathIntoGap)
  | .error .pathPastSpine => .ok (.error .pathPastSpine)
  | .error .pathIntoMixin => .ok (.error .pathIntoMixin)
  | .error .proofIncomplete => .ok (.error .proofIncomplete)

/-- Child results retain their error and their complete ordered allocation/write
trace. Only their successful return value is erased from the resource event. -/
inductive Effect where
  | indices (arena : Delimited.ArenaState) (outcome : Indices.Outcome Unit)
  | layout (arena : Delimited.ArenaState) (outcome : HashLayout.Outcome Unit)
  | reserve (layout : TypedArena.Layout) (arena : Delimited.ArenaState) (count : Nat)
      (result : Option Arena.Reservation)
  | initialized (pointer position : Nat) (bytes : Ssz.Bytes)
  | nodeInitialized (pointer position : Nat) (index : NatOperand)
      (shift depth : Nat) (source : Sum Nat Nat)

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

def liftIndices {α : Type} (arena : Delimited.ArenaState) (outcome : Indices.Outcome α) :
    Outcome α :=
  ⟨outcome.result.mapError Error.indices, outcome.used,
    [.indices arena ⟨outcome.result.map (fun _ => ()), outcome.used, outcome.effects⟩]⟩

def liftLayout {α : Type} (arena : Delimited.ArenaState) (outcome : HashLayout.Outcome α) :
    Outcome α :=
  ⟨outcome.result.mapError Error.layout, outcome.used,
    [.layout arena ⟨outcome.result.map (fun _ => ()), outcome.used, outcome.effects⟩]⟩

/-- The raw operation hashes both complete input borrows, including empty blobs. -/
def rawCombine (left right : Ssz.Bytes) : Ssz.Bytes :=
  (HashStream.combine ⟨left⟩ ⟨right⟩).data

theorem rawCombine_eq (left right : Ssz.Bytes) :
    rawCombine left right = Ssz.combine left right :=
  HashStream.combine_eq left right

theorem rawCombine_size (left right : Ssz.Bytes) : (rawCombine left right).size = 32 := by
  change (HashStream.combine ⟨left⟩ ⟨right⟩).size = 32
  exact HashStream.combine_size ⟨left⟩ ⟨right⟩

/-- Typed hash outputs have the native [u8;32] layout, not pointer alignment. -/
def hashLayout : TypedArena.Layout := ⟨32, 0⟩

structure HashSlice where
  values : List Ssz.Bytes
  reservation : Arena.Reservation

@[simp] theorem bind_error {α β : Type} (reason : Error) (used : Nat)
    (effects : List Effect) (next : α → Nat → Outcome β) :
    bind ⟨.error reason, used, effects⟩ next = ⟨.error reason, used, effects⟩ := rfl

@[simp] theorem bind_unchanged {α β : Type} (value : α) (used : Nat)
    (next : α → Nat → Outcome β) :
    bind (unchanged used (.ok value)) next = next value used := by
  simp only [bind, unchanged, List.nil_append]

theorem bind_retains_effects {α β : Type} (first : Outcome α)
    (next : α → Nat → Outcome β) :
    ∃ suffix, (bind first next).effects = first.effects ++ suffix := by
  cases result : first.result with
  | error reason => exact ⟨[], by simp [bind, result]⟩
  | ok value => exact ⟨(next value first.used).effects, by simp [bind, result]⟩

/-- Metadata is formed expected-first, exactly as the two from_u128 calls.
The input Nat describes a native u128; endpoint theorems discharge that bound
from logical index bit-length or physical slice representation as appropriate. -/
def countError (reason : CountReason) (expected actual : Nat)
    (arena : Delimited.ArenaState) : Outcome Error :=
  bind (liftLayout arena (HashLayout.fromWide (BitVec.ofNat 128 expected) arena)) fun left used =>
    let nextArena := { arena with used := used }
    bind (liftLayout nextArena (HashLayout.fromWide (BitVec.ofNat 128 actual) nextArena))
      fun right used => unchanged used (.ok (.count reason left right))

def failCount {α : Type} (reason : CountReason) (expected actual : Nat)
    (arena : Delimited.ArenaState) : Outcome α :=
  bind (countError reason expected actual arena) fun fault used =>
    unchanged used (.error fault)

/-- Exhaustion is the sole resource alternative. Host representation and width
errors cannot be used to excuse disagreement with the pinned semantics. -/
def IsExhausted : Error → Prop
  | .scratchExhausted => True
  | .indices (.arithmetic .scratchExhausted) => True
  | .layout (.codec (.primitive (.arithmetic .scratchExhausted))) => True
  | _ => False

inductive ResultRefines {α β : Type} (relation : α → β → Prop) :
    Except Error α → Except Ssz.Err β → Prop where
  | exhausted (reason : Error) (allowed : IsExhausted reason) (expected : Except Ssz.Err β) :
      ResultRefines relation (.error reason) expected
  | ok (actual : α) (expected : β) (related : relation actual expected) :
      ResultRefines relation (.ok actual) (.ok expected)
  | error (actual : Error) (expected : Ssz.Err)
      (same : eraseResult (.error actual : Except Error Unit) = .ok (.error expected)) :
      ResultRefines relation (.error actual) (.error expected)

abbrev Refines {α β : Type} (relation : α → β → Prop) (actual : Outcome α)
    (expected : Except Ssz.Err β) : Prop := ResultRefines relation actual.result expected

theorem ResultRefines.bind {α β γ δ : Type} (before : α → β → Prop)
    (after : γ → δ → Prop) (actual : Outcome α) (expected : Except Ssz.Err β)
    (next : α → Nat → Outcome γ) (specNext : β → Except Ssz.Err δ)
    (first : Refines before actual expected)
    (later : ∀ left right, before left right → ∀ used,
      Refines after (next left used) (specNext right)) :
    Refines after (bind actual next) (expected >>= specNext) := by
  rcases actual with ⟨result, used, effects⟩
  cases first with
  | exhausted reason allowed expected => exact .exhausted reason allowed _
  | ok left right related => exact later left right related used
  | error actual expected same => exact .error actual expected same

end SszNative.Proof

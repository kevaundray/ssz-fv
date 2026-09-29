import SszCodecTypes
import SszTypedArena
import Ssz.Type.Paths

set_option autoImplicit false

namespace SszNative.Indices

inductive Error where
  | arithmetic (reason : NatArithmetic.Failure)
  | notAGindex (index : NatOperand)
  | rootHasNoBranch
  | emptyRequest
  | repeatedIndex
  | nestedIndex (index : NatOperand)
  | noParts
  | noPartsMixin
  | noMixin
  | noChunkCount
  | notSteppable
  | noSuchField (ordinal : NatOperand)
  | noSuchOption (ordinal : NatOperand)
  | noSuchPosition (ordinal : NatOperand)
  deriving DecidableEq, Repr

def scratch : Error := .arithmetic .scratchExhausted

def eraseResult {α : Type} : Except Error α → Except Serialize.Host (Except Ssz.Err α)
  | .ok value => .ok (.ok value)
  | .error (.arithmetic reason) => .error (.arithmetic reason)
  | .error (.notAGindex index) => .ok (.error (.notAGindex index.value))
  | .error .rootHasNoBranch => .ok (.error .rootHasNoBranch)
  | .error .emptyRequest => .ok (.error .emptyRequest)
  | .error .repeatedIndex => .ok (.error .repeatedIndex)
  | .error (.nestedIndex index) => .ok (.error (.nestedIndex index.value))
  | .error .noParts => .ok (.error .noParts)
  | .error .noPartsMixin => .ok (.error .noPartsMixin)
  | .error .noMixin => .ok (.error .noMixin)
  | .error .noChunkCount => .ok (.error .noChunkCount)
  | .error .notSteppable => .ok (.error .notSteppable)
  | .error (.noSuchField ordinal) => .ok (.error (.noSuchField ordinal.value))
  | .error (.noSuchOption ordinal) => .ok (.error (.noSuchOption ordinal.value))
  | .error (.noSuchPosition ordinal) => .ok (.error (.noSuchPosition ordinal.value))

inductive PathStep where
  | position (ordinal : NatOperand)
  | length
  | activeFields
  | selector
  deriving DecidableEq, Repr

def PathStep.erase : PathStep → Ssz.PathStep
  | .position ordinal => .position ordinal.value
  | .length => .length
  | .activeFields => .activeFields
  | .selector => .selector

structure ChunkPosition where
  chunk : NatOperand
  start : NatOperand
  stop : NatOperand
  deriving DecidableEq, Repr

def ChunkPosition.erase (position : ChunkPosition) : Ssz.ChunkPosition :=
  ⟨position.chunk.value, position.start.value, position.stop.value⟩

/-- An attempted arithmetic call records its entire retained scratch state.
Outer reservations and completed initializers are separate ordered events. -/
inductive Effect where
  | arithmetic (initialUsed : Nat) (outcome : NatArithmetic.Outcome NatOperand)
  | divide (initialUsed : Nat) (outcome : NatArithmetic.Outcome (NatOperand × BitVec 64))
  | reserve (layout : TypedArena.Layout) (count initialUsed : Nat)
      (result : Option Arena.Reservation)
  | initialized (pointer slot : Nat) (value : NatOperand)
  | sorted (pointer : Nat) (values : List NatOperand)
  deriving Repr

structure Outcome (α : Type) where
  result : Except Error α
  used : Nat
  effects : List Effect

/-- Nat occupies sixteen bytes with eight-byte alignment on both measured ABIs. -/
def natLayout : TypedArena.Layout := ⟨16, 3⟩

/-- The reservation is retained even for an empty slice: its pointer is the
alignment-valued dangling pointer returned by the native zero-count branch. -/
structure NatSlice where
  values : List NatOperand
  reservation : Arena.Reservation
  deriving Repr

def unchanged {α : Type} (used : Nat) (result : Except Error α) : Outcome α :=
  ⟨result, used, []⟩

def bind {α β : Type} (first : Outcome α) (next : α → Nat → Outcome β) : Outcome β :=
  match first.result with
  | .error reason => ⟨.error reason, first.used, first.effects⟩
  | .ok value =>
      let second := next value first.used
      ⟨second.result, second.used, first.effects ++ second.effects⟩

def arithmetic (used : Nat) (outcome : NatArithmetic.Outcome NatOperand) : Outcome NatOperand :=
  ⟨outcome.result.mapError Error.arithmetic, outcome.used, [.arithmetic used outcome]⟩

def divide (used : Nat) (outcome : NatArithmetic.Outcome (NatOperand × BitVec 64)) :
    Outcome (NatOperand × BitVec 64) :=
  ⟨outcome.result.mapError Error.arithmetic, outcome.used, [.divide used outcome]⟩

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

theorem eraseResult_map {α β : Type} (result : Except Error α) (f : α → β) :
    eraseResult (result.map f) = (eraseResult result).map (fun value => value.map f) := by
  cases result with
  | ok value => rfl
  | error reason => cases reason <;> rfl

end SszNative.Indices

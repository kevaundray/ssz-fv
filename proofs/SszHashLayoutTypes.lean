import SszCodecError
import SszCodecTypesProofs
import SszNatMul
import SszNatDivision
import SszMerkleAccumulatorRefinement
import SszMerkleProgressiveRefinement
import SszMerkleWordsActive
import Ssz.Codec.Root

set_option autoImplicit false

namespace SszNative.HashLayout

open Codec (Desc Value)

/-- Hashing extends, rather than reinterprets, the accepted raw codec errors. -/
inductive Error where
  | codec (reason : Codec.Error)
  | merkle (reason : MerkleAccumulator.Error)
  | layoutFieldCount (active fields : NatOperand)
  | unionSelectorRange (selector low high : NatOperand)

def eraseResult {α : Type} : Except Error α → Except Serialize.Host (Except Ssz.Err α)
  | .ok value => .ok (.ok value)
  | .error (.codec reason) => Codec.eraseResult (.error reason)
  | .error (.merkle (.merkleizeLimit count capacity)) =>
      .ok (.error (.merkleizeLimit count.value capacity.value))
  | .error (.merkle .outputTooSmall) => .error .outputTooSmall
  | .error (.layoutFieldCount active fields) =>
      .ok (.error (.layoutFieldCount active.value fields.value))
  | .error (.unionSelectorRange selector low high) =>
      .ok (.error (.unionSelectorRange selector.value low.value high.value))

def wrongType : Error := .codec (.primitive .wrongType)
def arithmeticError (reason : NatArithmetic.Failure) : Error :=
  .codec (.primitive (.arithmetic reason))

/-- Each helper attempt keeps its original operands, input cursor, reservation,
and all written limbs. Failed attempts are recorded, not rolled back. -/
inductive Effect where
  | fromWide (wide : BitVec 128) (arena : Delimited.ArenaState)
      (outcome : NatArithmetic.Outcome NatOperand)
  | add (left right : NatOperand) (arena : Delimited.ArenaState)
      (outcome : NatArithmetic.Outcome NatOperand)
  | mul (left right : NatOperand) (arena : Delimited.ArenaState)
      (outcome : NatArithmetic.Outcome NatOperand)
  | divide (operand : NatOperand) (divisor : BitVec 64) (arena : Delimited.ArenaState)
      (outcome : NatArithmetic.Outcome (NatOperand × BitVec 64))

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

def lift {α : Type} (used : Nat) (result : Except Error α) : Outcome α :=
  unchanged used result

@[simp] theorem bind_error {α β : Type} (used : Nat) (effects : List Effect)
    (reason : Error) (next : α → Nat → Outcome β) :
    bind ⟨.error reason, used, effects⟩ next = ⟨.error reason, used, effects⟩ := rfl

@[simp] theorem bind_ok {α β : Type} (used : Nat) (value : α)
    (next : α → Nat → Outcome β) :
    bind (unchanged used (.ok value)) next = next value used := by
  simp only [bind, unchanged, List.nil_append]

 theorem eraseResult_map {α β : Type} (result : Except Error α) (f : α → β) :
    eraseResult (result.map f) = (eraseResult result).map (fun value => value.map f) := by
  cases result with
  | ok value => rfl
  | error reason =>
      cases reason with
      | codec reason => exact Codec.eraseResult_map (.error reason) f
      | merkle reason => cases reason <;> rfl
      | layoutFieldCount _ _ | unionSelectorRange _ _ _ => rfl

end SszNative.HashLayout

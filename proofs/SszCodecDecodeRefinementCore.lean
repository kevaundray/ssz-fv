import SszCodecDecode
import SszFixedSizeProofs

set_option autoImplicit false

namespace SszNative.CodecDecode

open Codec (Desc Error)

/-- The only admitted host alternative is the decoder's actual resource error.
No representation failure, future execution, or successful allocation is assumed. -/
def Refines {α β : Type} (erase : α → β) (outcome : Outcome α)
    (expected : Except Ssz.Err β) : Prop :=
  Codec.eraseResult (outcome.result.map erase) = .ok expected ∨
    outcome.result = .error scratch

def nodeErase (node : Node) : Ssz.Value := node.value.erase

def nodesErase (nodes : List Node) : List Ssz.Value := nodes.map nodeErase

theorem node_values_erase (nodes : List Node) :
    Codec.Value.eraseList (Node.values nodes) = nodesErase nodes := by
  induction nodes with
  | nil => rfl
  | cons node rest ih => simp only [Node.values, Codec.Value.eraseList, nodesErase,
      List.map_cons, nodeErase] at *; rw [ih]

theorem refines_unchanged {α β : Type} (erase : α → β) (value : α) (used : Nat) :
    Refines erase (unchanged used (.ok value)) (.ok (erase value)) := by
  exact Or.inl rfl

theorem refines_scratch {α β : Type} (erase : α → β) (outcome : Outcome α)
    (expected : Except Ssz.Err β) (failed : outcome.result = .error scratch) :
    Refines erase outcome expected := Or.inr failed

/-- Result-level composition, independent of ordered effects and cursor changes. -/
theorem refines_bind {α β γ δ : Type} (eraseFirst : α → γ) (eraseNext : β → δ)
    (first : Outcome α) (next : α → Nat → Outcome β)
    (expected : Except Ssz.Err γ) (continuation : γ → Except Ssz.Err δ)
    (firstRefines : Refines eraseFirst first expected)
    (nextRefines : ∀ value used, Refines eraseNext (next value used) (continuation (eraseFirst value))) :
    Refines eraseNext (bind first next) (expected.bind continuation) := by
  rcases firstRefines with correct | exhausted
  · cases result : first.result with
    | ok value =>
      have equal : Except.ok (eraseFirst value) = expected := by
        simpa only [result, Except.map, Codec.eraseResult, Except.ok.injEq] using correct
      subst expected
      simpa only [bind, result, Except.bind, Refines] using nextRefines value first.used
    | error reason =>
      cases reason with
      | primitive reason =>
        cases reason <;>
          simp [result, Except.map, Codec.eraseResult, Serialize.eraseResult] at correct <;>
          subst expected <;>
          exact Or.inl (by simp only [bind, result, Except.map, Codec.eraseResult,
            Serialize.eraseResult, Except.bind])
      | offsetOverflow _ | unknownSelector _ | scopeTooSmall _ _ | scopeUndivided _ _
      | scopeWidthless | firstOffset _ _ | offsetUnordered | offsetPastScope
      | offsetUnaligned | offsetBelowTable | truncated | notABit _ | paddingBits
      | emptyEncoding | noDelimiter | trailingZeros | noSelector =>
        simp only [result, Except.map, Codec.eraseResult, Except.ok.injEq] at correct
        subst expected
        left
        simp only [bind, result, Except.map, Codec.eraseResult, Except.bind]
  · right
    simp only [bind, exhausted]

theorem count_value (count : Nat) (physical : count < 2 ^ 64) :
    (Serialize.count count).value = count := by
  simp only [Serialize.count, NatOperand.value, NatOperand.words, Limbs.value,
    Nat.mul_zero, Nat.add_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt physical]

theorem exact_refines (expected : NatOperand) (actual used : Nat)
    (physical : actual < 2 ^ 64) :
    Refines (fun value : Unit => value) (exact expected actual used)
      (if actual = expected.value then .ok () else .error (.scope expected.value actual)) := by
  left
  by_cases scope : expected.value = actual
  · simp only [exact, scope, ↓reduceIte, unchanged, Except.map, Codec.eraseResult]
  · have reverse : actual ≠ expected.value := Ne.symm scope
    simp only [exact, scope, reverse, ↓reduceIte, unchanged, Except.map, Codec.eraseResult,
      Serialize.eraseResult, count_value actual physical]

theorem narrow_fits (number : NatOperand) (reason : Error) (used : Nat)
    (fits : number.value < 2 ^ 64) :
    narrow number reason used = unchanged used (.ok number.value) := by
  simp only [narrow, fits, ↓reduceIte]

theorem fixedSize_refines (desc : Desc) (arena : Delimited.ArenaState) :
    Refines (Option.map NatOperand.value) (fixedSize desc arena) (.ok desc.erase.fixedSize) := by
  rcases FixedSize.fixedSize_refines desc arena with success | exhausted
  · left
    cases result : (FixedSize.fixedSize desc arena).result with
    | error reason => simp only [result, Except.map] at success; cases success
    | ok width =>
      simp only [result, Except.map, Except.ok.injEq] at success
      simp only [fixedSize, result, Except.map, Except.mapError, Codec.eraseResult, success]
  · right
    simp only [fixedSize, exhausted, Except.mapError, scratch]

end SszNative.CodecDecode

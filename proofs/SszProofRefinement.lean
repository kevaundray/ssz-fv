import SszProofTypes
import SszHashLayoutRefinementCore

set_option autoImplicit false

namespace SszNative.Proof

theorem liftLayout_refines {α β : Type} (relation : α → β → Prop)
    (arena : Delimited.ArenaState) (outcome : HashLayout.Outcome α)
    (expected : Except Ssz.Err β) (refined : HashLayout.Refines relation outcome expected) :
    Refines relation (liftLayout arena outcome) expected := by
  rcases outcome with ⟨result, used, effects⟩
  cases refined with
  | exhausted expected =>
      exact .exhausted (.layout (HashLayout.arithmeticError .scratchExhausted)) trivial expected
  | ok actual expected related => exact .ok actual expected related
  | error actual expected same => exact .error (.layout actual) expected same

theorem ResultRefines.map {α β γ δ : Type} (relation : α → β → Prop)
    (target : γ → δ → Prop) (actual : Except Error α) (expected : Except Ssz.Err β)
    (f : α → γ) (g : β → δ) (refined : ResultRefines relation actual expected)
    (mapped : ∀ left right, relation left right → target (f left) (g right)) :
    ResultRefines target (actual.map f) (expected.map g) := by
  cases refined with
  | exhausted reason allowed expected => exact .exhausted reason allowed _
  | ok left right related => exact .ok _ _ (mapped left right related)
  | error actual expected same => exact .error actual expected same

theorem countError_refines (reason : CountReason) (expected actual : Nat)
    (arena : Delimited.ArenaState) (expectedFits : expected < 2^128)
    (actualFits : actual < 2^128) :
    Refines (fun fault semantic =>
      eraseResult (.error fault : Except Error Unit) = .ok (.error semantic))
      (countError reason expected actual arena) (.ok (reason.erase expected actual)) := by
  unfold countError
  have first := liftLayout_refines (fun operand number => operand.value = number) arena
    (HashLayout.fromWide (BitVec.ofNat 128 expected) arena) _
    (HashLayout.fromWide_refines (BitVec.ofNat 128 expected) arena)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt expectedFits] at first
  apply ResultRefines.bind (fun (operand : NatOperand) (number : Nat) => operand.value = number)
    _ (liftLayout arena (HashLayout.fromWide (BitVec.ofNat 128 expected) arena)) (.ok expected)
    _ (fun number => .ok (reason.erase number actual)) first
  intro left number same used
  have second := liftLayout_refines (fun (operand : NatOperand) (number : Nat) => operand.value = number)
    { arena with used := used }
    (HashLayout.fromWide (BitVec.ofNat 128 actual) { arena with used := used })
    (.ok (BitVec.ofNat 128 actual).toNat)
    (HashLayout.fromWide_refines (BitVec.ofNat 128 actual) { arena with used := used })
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt actualFits] at second
  apply ResultRefines.bind (fun (operand : NatOperand) (number : Nat) => operand.value = number)
    _ (liftLayout { arena with used := used }
      (HashLayout.fromWide (BitVec.ofNat 128 actual) { arena with used := used })) (.ok actual)
    _ (fun number' => .ok (reason.erase number number')) second
  intro right number' same' used'
  exact .ok _ _ (by simp only [eraseResult, same, same'])

theorem failCount_refines {α : Type} (reason : CountReason) (expected actual : Nat)
    (arena : Delimited.ArenaState) (expectedFits : expected < 2^128)
    (actualFits : actual < 2^128) :
    Refines Eq (failCount (α := α) reason expected actual arena)
      (.error (reason.erase expected actual)) := by
  unfold failCount
  apply ResultRefines.bind
    (fun fault semantic => eraseResult (.error fault : Except Error Unit) = .ok (.error semantic))
    Eq _ _ _ _ (countError_refines reason expected actual arena expectedFits actualFits)
  intro fault semantic same used
  exact .error fault semantic same

/-- The premise records the already-completed first call, never a future run. -/
theorem ResultRefines.bind_success {α β γ δ : Type} (before : α → β → Prop)
    (after : γ → δ → Prop) (actual : Outcome α) (expected : Except Ssz.Err β)
    (next : α → Nat → Outcome γ) (specNext : β → Except Ssz.Err δ)
    (first : Refines before actual expected)
    (later : ∀ left right, actual.result = .ok left → before left right → ∀ used,
      Refines after (next left used) (specNext right)) :
    Refines after (SszNative.Proof.bind actual next) (expected >>= specNext) := by
  rcases actual with ⟨result, used, effects⟩
  cases first with
  | exhausted reason allowed expected => exact .exhausted reason allowed _
  | ok left right related => exact later left right rfl related used
  | error actual expected same => exact .error actual expected same

/-- No refinement theorem assumes success or enough scratch for a later call. -/
theorem Refines.success {α : Type} (actual : Outcome α) (expected : Except Ssz.Err α)
    (refined : Refines Eq actual expected) (value : α) (success : actual.result = .ok value) :
    expected = .ok value := by
  rw [Refines, success] at refined
  cases refined with
  | ok actual expected same => cases same; rfl

end SszNative.Proof

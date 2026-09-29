import SszHashLayout
import SszHashLayoutArithmeticProofs
import SszHashLayoutStream
import SszHashLayoutPackedProofs
import SszHashLayoutNestedProofs

set_option autoImplicit false

namespace SszNative.HashLayout

/-- The only permitted interruption is the actual returned ScratchExhausted.
In particular BadRepresentation and OutputTooSmall cannot hide a disagreement. -/
inductive ResultRefines {α β : Type} (relation : α → β → Prop) :
    Except Error α → Except Ssz.Err β → Prop where
  | exhausted (expected : Except Ssz.Err β) :
      ResultRefines relation (.error (arithmeticError .scratchExhausted)) expected
  | ok (actual : α) (expected : β) (related : relation actual expected) :
      ResultRefines relation (.ok actual) (.ok expected)
  | error (actual : Error) (expected : Ssz.Err)
      (same : eraseResult (.error actual : Except Error Unit) = .ok (.error expected)) :
      ResultRefines relation (.error actual) (.error expected)

abbrev Refines {α β : Type} (relation : α → β → Prop) (actual : Outcome α)
    (expected : Except Ssz.Err β) : Prop := ResultRefines relation actual.result expected

theorem ResultRefines.map_expected {α β γ : Type} (relation : α → β → Prop)
    (target : α → γ → Prop) (actual : Except Error α) (expected : Except Ssz.Err β)
    (f : β → γ) (refined : ResultRefines relation actual expected)
    (mapped : ∀ left right, relation left right → target left (f right)) :
    ResultRefines target actual (expected.map f) := by
  cases refined with
  | exhausted expected => exact .exhausted _
  | ok left right related => exact .ok left (f right) (mapped left right related)
  | error actual expected same => exact .error actual expected same

theorem ResultRefines.erase_or_exhausted {α : Type} (actual : Except Error α)
    (expected : Except Ssz.Err α) (refined : ResultRefines Eq actual expected) :
    eraseResult actual = .ok expected ∨ actual = .error (arithmeticError .scratchExhausted) := by
  cases refined with
  | exhausted expected => exact Or.inr rfl
  | ok left right same => subst right; exact Or.inl rfl
  | error actual expected same =>
      apply Or.inl
      cases actual with
      | codec reason =>
          cases reason with
          | primitive reason =>
              cases reason <;>
                simp only [eraseResult, Codec.eraseResult, Serialize.eraseResult,
                  Except.ok.injEq, Except.error.injEq] at same ⊢ <;> cases same <;> rfl
          | _ =>
              simp only [eraseResult, Codec.eraseResult,
                Except.ok.injEq, Except.error.injEq] at same ⊢ <;> cases same <;> rfl
      | merkle reason =>
          cases reason <;> simp only [eraseResult,
            Except.ok.injEq, Except.error.injEq] at same ⊢ <;> cases same <;> rfl
      | _ =>
          simp only [eraseResult, Except.ok.injEq, Except.error.injEq] at same ⊢
          cases same
          rfl

theorem ResultRefines.of_erased_map {α β : Type} (actual : Except Error α)
    (expected : Except Ssz.Err β) (f : α → β)
    (same : eraseResult (actual.map f) = .ok expected) :
    ResultRefines (fun left right => f left = right) actual expected := by
  cases actual with
  | ok value =>
      simp only [Except.map, eraseResult, Except.ok.injEq] at same
      subst expected
      exact .ok value (f value) rfl
  | error reason =>
      cases expected with
      | ok value =>
          cases reason with
          | codec reason =>
              cases reason with
              | primitive reason => cases reason <;> cases same
              | _ => cases same
          | merkle reason => cases reason <;> cases same
          | _ => cases same
      | error fault =>
          apply ResultRefines.error reason fault
          have mapped := congrArg
            (fun result : Except Serialize.Host (Except Ssz.Err β) =>
              result.map (fun inner => inner.map (fun _ => ()))) same
          rw [← eraseResult_map] at mapped
          exact mapped

theorem ResultRefines.bind {α β γ δ : Type} (before : α → β → Prop)
    (after : γ → δ → Prop) (actual : Outcome α) (expected : Except Ssz.Err β)
    (next : α → Nat → Outcome γ) (specNext : β → Except Ssz.Err δ)
    (first : Refines before actual expected)
    (later : ∀ left right, before left right → ∀ used,
      Refines after (next left used) (specNext right)) :
    Refines after (bind actual next) (expected >>= specNext) := by
  rcases actual with ⟨result, used, effects⟩
  cases first with
  | exhausted expected => exact .exhausted _
  | ok left right related =>
      change ResultRefines after (next left used).result (specNext right)
      exact later left right related used
  | error actual expected same => exact .error actual expected same

theorem Refines.arithmetic {α : Type} (actual : Outcome α) (expected : Nat)
    (allowed : OnlyExhaustion actual) (value : α → Nat)
    (correct : ∀ result, actual.result = .ok result → value result = expected) :
    Refines (fun result number => value result = number) actual (.ok expected) := by
  cases resultEq : actual.result with
  | error reason =>
      have reasonEq := allowed reason resultEq
      rw [reasonEq] at resultEq
      rw [Refines, resultEq]
      exact .exhausted _
  | ok result =>
      rw [Refines, resultEq]
      exact .ok result expected (correct result resultEq)

theorem fromWide_refines (wide : BitVec 128) (arena : Delimited.ArenaState) :
    Refines (fun operand number => operand.value = number) (fromWide wide arena) (.ok wide.toNat) :=
  Refines.arithmetic _ _ (fromWide_onlyExhaustion wide arena) NatOperand.value
    (fun result success => fromWide_value wide arena result success)

theorem mul_refines (left right : NatOperand) (arena : Delimited.ArenaState) :
    Refines (fun operand number => operand.value = number) (mul left right arena)
      (.ok (left.value * right.value)) :=
  Refines.arithmetic _ _ (mul_onlyExhaustion left right arena) NatOperand.value
    (fun result success => mul_value left right arena result success)

theorem ceilDiv_refines (operand : NatOperand) (divisor : BitVec 64)
    (arena : Delimited.ArenaState) (nonzero : divisor ≠ 0) :
    Refines (fun result number => result.value = number) (ceilDiv operand divisor arena)
      (.ok ((operand.value + divisor.toNat - 1) / divisor.toNat)) :=
  Refines.arithmetic _ _ (ceilDiv_onlyExhaustion operand divisor arena nonzero) NatOperand.value
    (fun result success => ceilDiv_value operand divisor arena nonzero result success)

/-- Arrays occur in the specification relation, never in the operational layout. -/
inductive LeavesRefines : Leaves → Ssz.Leaves → Prop where
  | packed (view : Packed) (chunks : Array Ssz.Bytes)
      (count : view.count = chunks.size)
      (each : ∀ index (inside : index < view.count),
        packedChunk view index = .ok (chunks[index]'(by omega))) :
      LeavesRefines (.packed view) (.packed chunks)
  | nested (view : Nested) (slots : List (Option (Ssz.Desc × Ssz.Value)))
      (count : view.count = slots.length)
      (each : ∀ index, (view.at index).map erasePair = slots[index]?.getD none) :
      LeavesRefines (.nested view) (.nested slots)

def LayoutRefines (actual : Layout) (expected : Ssz.MerkleLayout) : Prop :=
  LeavesRefines actual.leaves expected.leaves ∧
    actual.limit.map NatOperand.value = expected.limit ∧ actual.mixin = expected.mixin

theorem LayoutRefines.count (actual : Layout) (expected : Ssz.MerkleLayout)
    (related : LayoutRefines actual expected) : actual.count = expected.leaves.count := by
  rcases actual with ⟨leaves, limit, mixin⟩
  rcases expected with ⟨specLeaves, specLimit, specMixin⟩
  cases related.1 with
  | packed view chunks count each => exact count
  | nested view slots count each => exact count

theorem packing_refines (view : Packed) (data : Ssz.Bytes)
    (bytes : RepresentsBytes view data) (limit : Option NatOperand) (mixin : Option Ssz.Bytes) :
    LayoutRefines ⟨.packed view, limit, mixin⟩
      (Ssz.MerkleLayout.packing (Ssz.packBytes data) (limit.map NatOperand.value) mixin) := by
  refine ⟨.packed view (Ssz.packBytes data) (packed_count_refines view data bytes) ?_, rfl, rfl⟩
  intro index inside
  exact packedChunk_refines view data bytes index inside

theorem nesting_refines (view : Nested) (slots : List (Option (Ssz.Desc × Ssz.Value)))
    (count : view.count = slots.length)
    (each : ∀ index, (view.at index).map erasePair = slots[index]?.getD none)
    (limit : Option NatOperand) (mixin : Option Ssz.Bytes) :
    LayoutRefines ⟨.nested view, limit, mixin⟩
      (Ssz.MerkleLayout.nesting slots (limit.map NatOperand.value) mixin) :=
  ⟨.nested view slots count each, rfl, rfl⟩

end SszNative.HashLayout

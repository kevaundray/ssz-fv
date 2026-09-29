import SszIndicesPaths
import SszIndicesDescriptorRefinement
import Ssz.Proofs.Type.PathLaws

set_option autoImplicit false

namespace SszNative.Indices

@[simp] theorem arithmetic_success_iff (used : Nat) (actual : NatArithmetic.Outcome NatOperand)
    (value : NatOperand) :
    (arithmetic used actual).result = .ok value ↔ actual.result = .ok value := by
  cases returned : actual.result <;> simp [arithmetic, returned, Except.mapError]

@[simp] theorem divide_success_iff (used : Nat)
    (actual : NatArithmetic.Outcome (NatOperand × BitVec 64)) (value : NatOperand × BitVec 64) :
    (divide used actual).result = .ok value ↔ actual.result = .ok value := by
  cases returned : actual.result <;> simp [divide, returned, Except.mapError]

/-- Resource failures remain observable host errors. Whenever the native call
returns a semantic result, both its value and its exact refusal agree with the
pinned specification. This relation does not assert resource availability. -/
def PathRefines {α β : Type} (erase : α → β) (actual : Except Error α)
    (expected : Except Ssz.Err β) : Prop :=
  ∀ observed, eraseResult (actual.map erase) = .ok observed → observed = expected

namespace PathRefines

 theorem of_eq {α β : Type} {erase : α → β} {actual : Except Error α}
    {expected : Except Ssz.Err β}
    (same : eraseResult (actual.map erase) = .ok expected) :
    PathRefines erase actual expected := by
  intro observed observedEq
  exact Except.ok.inj (observedEq.symm.trans same)

 theorem ok {α β : Type} (erase : α → β) (value : α) :
    PathRefines erase (.ok value) (.ok (erase value)) := by
  exact of_eq rfl

 theorem arithmetic_error {α β : Type} (erase : α → β)
    (reason : NatArithmetic.Failure) (expected : Except Ssz.Err β) :
    PathRefines erase (.error (.arithmetic reason)) expected := by
  intro observed observedEq
  cases observedEq

 theorem success {α β : Type} {erase : α → β} {actual : Except Error α}
    {expected : Except Ssz.Err β} (refined : PathRefines erase actual expected)
    (value : α) (returned : actual = .ok value) : expected = .ok (erase value) := by
  exact (refined (.ok (erase value)) (by rw [returned]; rfl)).symm

 theorem arithmetic {α β : Type} (erase : α → β)
    (actual : NatArithmetic.Outcome α) (expected : β)
    (correct : ∀ value, actual.result = .ok value → erase value = expected) :
    PathRefines erase (actual.result.mapError Error.arithmetic) (.ok expected) := by
  cases returned : actual.result with
  | error reason => exact arithmetic_error erase reason (.ok expected)
  | ok value =>
      have valueEq := correct value returned
      simpa only [Except.mapError, valueEq] using ok erase value

 theorem bind {α β γ δ : Type} (first : Outcome α) (next : α → Nat → Outcome γ)
    (eraseFirst : α → β) (eraseNext : γ → δ)
    (expectedFirst : Except Ssz.Err β) (expectedNext : β → Except Ssz.Err δ)
    (firstRefines : PathRefines eraseFirst first.result expectedFirst)
    (nextRefines : ∀ value, first.result = .ok value →
      PathRefines eraseNext (next value first.used).result (expectedNext (eraseFirst value))) :
    PathRefines eraseNext (Indices.bind first next).result
      (expectedFirst >>= expectedNext) := by
  cases returned : first.result with
  | ok value =>
      rw [firstRefines.success value returned]
      simpa only [Indices.bind, returned, Bind.bind, Except.bind] using
        nextRefines value returned
  | error reason =>
      have semanticError (fault : Ssz.Err)
          (sourceError : eraseResult ((.error reason : Except Error α).map eraseFirst) =
            .ok (.error fault))
          (targetError : eraseResult ((.error reason : Except Error γ).map eraseNext) =
            .ok (.error fault)) :
          PathRefines eraseNext (Indices.bind first next).result
            (expectedFirst >>= expectedNext) := by
        have same := firstRefines (.error fault) (by rw [returned]; exact sourceError)
        rw [← same]
        apply of_eq
        simpa only [Indices.bind, returned, Bind.bind, Except.bind] using targetError
      cases reason with
      | arithmetic reason =>
          simp only [Indices.bind, returned]
          exact arithmetic_error eraseNext reason _
      | notAGindex index => exact semanticError (.notAGindex index.value) rfl rfl
      | rootHasNoBranch => exact semanticError .rootHasNoBranch rfl rfl
      | emptyRequest => exact semanticError .emptyRequest rfl rfl
      | repeatedIndex => exact semanticError .repeatedIndex rfl rfl
      | nestedIndex index => exact semanticError (.nestedIndex index.value) rfl rfl
      | noParts => exact semanticError .noParts rfl rfl
      | noPartsMixin => exact semanticError .noPartsMixin rfl rfl
      | noMixin => exact semanticError .noMixin rfl rfl
      | noChunkCount => exact semanticError .noChunkCount rfl rfl
      | notSteppable => exact semanticError .notSteppable rfl rfl
      | noSuchField ordinal => exact semanticError (.noSuchField ordinal.value) rfl rfl
      | noSuchOption ordinal => exact semanticError (.noSuchOption ordinal.value) rfl rfl
      | noSuchPosition ordinal => exact semanticError (.noSuchPosition ordinal.value) rfl rfl

 theorem map {α β γ δ : Type} (actual : Except Error α) (erase : α → β)
    (expected : Except Ssz.Err β) (f : α → γ) (g : β → δ) (eraseOut : γ → δ)
    (commutes : ∀ value, eraseOut (f value) = g (erase value))
    (refined : PathRefines erase actual expected) :
    PathRefines eraseOut (actual.map f) (expected.map g) := by
  cases returned : actual with
  | ok value =>
      rw [refined.success value returned]
      exact of_eq (by simp only [Except.map, eraseResult, commutes])
  | error reason =>
      have semanticError (fault : Ssz.Err)
          (sourceError : eraseResult ((.error reason : Except Error α).map erase) =
            .ok (.error fault))
          (targetError : eraseResult ((.error reason : Except Error γ).map eraseOut) =
            .ok (.error fault)) :
          PathRefines eraseOut ((.error reason : Except Error α).map f) (expected.map g) := by
        have same := refined (.error fault) (by rw [returned]; exact sourceError)
        rw [← same]
        exact of_eq targetError
      cases reason with
      | arithmetic reason => exact arithmetic_error eraseOut reason _
      | notAGindex index => exact semanticError (.notAGindex index.value) rfl rfl
      | rootHasNoBranch => exact semanticError .rootHasNoBranch rfl rfl
      | emptyRequest => exact semanticError .emptyRequest rfl rfl
      | repeatedIndex => exact semanticError .repeatedIndex rfl rfl
      | nestedIndex index => exact semanticError (.nestedIndex index.value) rfl rfl
      | noParts => exact semanticError .noParts rfl rfl
      | noPartsMixin => exact semanticError .noPartsMixin rfl rfl
      | noMixin => exact semanticError .noMixin rfl rfl
      | noChunkCount => exact semanticError .noChunkCount rfl rfl
      | notSteppable => exact semanticError .notSteppable rfl rfl
      | noSuchField ordinal => exact semanticError (.noSuchField ordinal.value) rfl rfl
      | noSuchOption ordinal => exact semanticError (.noSuchOption ordinal.value) rfl rfl
      | noSuchPosition ordinal => exact semanticError (.noSuchPosition ordinal.value) rfl rfl

end PathRefines

/-- The paired raw variants erase to the same first selector slot. No distinctness
or declaration-validity hypothesis is needed, even for duplicated selectors. -/
theorem unionOption_refines (variants : List (NatOperand × Codec.Desc))
    (ordinal : NatOperand) :
    (unionOption variants ordinal).map Codec.Desc.erase =
      ((variants.map (fun variant => variant.1.value)).idxOf? ordinal.value).map
        (fun slot => (Codec.Desc.eraseVariants variants)[slot]!) := by
  induction variants with
  | nil => rfl
  | cons variant rest ih =>
      obtain ⟨selector, child⟩ := variant
      by_cases same : selector.value = ordinal.value
      · simp [unionOption, same, List.idxOf?_cons, Codec.Desc.eraseVariants]
      · simp only [unionOption, nativeCmp_eq_iff, ↓reduceIte, List.map_cons,
          List.idxOf?_cons, beq_iff_eq, same, Codec.Desc.eraseVariants]
        cases found : (rest.map (fun variant => variant.1.value)).idxOf? ordinal.value with
        | none => simpa [found] using ih
        | some slot => simpa [found] using ih

/-- Empty paths select the root even for raw invalid primitive declarations. -/
theorem generalizedIndex_nil_refines (shape : Codec.Desc) (base capacity used : Nat) :
    eraseResult ((generalizedIndex shape [] base capacity used).result.map NatOperand.value) =
      .ok (Ssz.getGeneralizedIndex shape.erase []) := by
  rfl

/-- Basic types reject every nonempty step before considering its kind or width. -/
theorem resolveStep_uint_refines (width : NatOperand) (step : PathStep)
    (base capacity used : Nat) :
    eraseResult ((resolveStep (.primitive (.uint width)) step base capacity used).result.map
      (fun result => (result.1.value, result.2.map Codec.Desc.erase))) =
      .ok ((Codec.Desc.primitive (.uint width)).erase.resolveStep step.erase) := by
  rfl

end SszNative.Indices

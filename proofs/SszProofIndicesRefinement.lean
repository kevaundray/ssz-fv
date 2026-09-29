import SszProofRefinement

set_option autoImplicit false

namespace SszNative.Proof

/-- Rewrap the index subsystem without flattening, reordering, or discarding any
of its retained effects. The only alternative is its actually returned scratch error. -/
theorem liftIndices_erased_refines {α β : Type} (arena : Delimited.ArenaState)
    (actual : Indices.Outcome α) (expected : Except Ssz.Err β) (erase : α → β)
    (refined : Indices.eraseResult (actual.result.map erase) = .ok expected ∨
      actual.result = .error Indices.scratch) :
    Refines (fun left right => erase left = right) (liftIndices arena actual) expected := by
  rcases refined with same | exhausted
  · cases result : actual.result with
    | ok value =>
        simp only [result, Except.map, Indices.eraseResult, Except.ok.injEq] at same
        subst expected
        change ResultRefines _ (actual.result.mapError Error.indices) _
        rw [result]
        exact .ok value (erase value) rfl
    | error reason =>
        cases expected with
        | ok value =>
            rw [result] at same
            cases reason <;> cases same
        | error fault =>
            change ResultRefines _ (actual.result.mapError Error.indices) _
            rw [result]
            apply ResultRefines.error (.indices reason) fault
            rw [result] at same
            cases reason <;> simp_all [Except.map, eraseResult, Indices.eraseResult]
  · change ResultRefines _ (actual.result.mapError Error.indices) _
    rw [exhausted]
    exact .exhausted (.indices Indices.scratch) trivial expected

theorem liftIndices_frontier_refines (arena : Delimited.ArenaState)
    (actual : Indices.Outcome Indices.NatSlice) (expected : Except Ssz.Err (List Nat))
    (refined : Indices.eraseResult (actual.result.map (fun slice => slice.values.map NatOperand.value)) =
        .ok expected ∨ actual.result = .error Indices.scratch) :
    Refines (fun slice values => slice.values.map NatOperand.value = values)
      (liftIndices arena actual) expected :=
  liftIndices_erased_refines arena actual expected (fun slice => slice.values.map NatOperand.value) refined

end SszNative.Proof

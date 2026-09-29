import SszIndicesArithmeticPhysical
import SszNatShiftResources

set_option autoImplicit false

namespace SszNative.Indices

theorem arithmetic_success (used : Nat) (outcome : NatArithmetic.Outcome NatOperand)
    (result : NatOperand) (success : (arithmetic used outcome).result = .ok result) :
    outcome.result = .ok result := by
  cases observed : outcome.result with
  | error reason =>
      simp only [arithmetic, observed, Except.mapError] at success
      cases success
  | ok value =>
      simp only [arithmetic, observed, Except.mapError, Except.ok.injEq] at success
      cases success
      rfl

theorem arithmetic_error (used : Nat) (outcome : NatArithmetic.Outcome NatOperand)
    (reason : Error) (failure : (arithmetic used outcome).result = .error reason) :
    ∃ source, outcome.result = .error source ∧ reason = .arithmetic source := by
  cases observed : outcome.result with
  | error source =>
      simp only [arithmetic, observed, Except.mapError, Except.error.injEq] at failure
      exact ⟨source, rfl, failure.symm⟩
  | ok value =>
      simp only [arithmetic, observed, Except.mapError] at failure
      cases failure

theorem parent_success_physical (index : NatOperand) (base capacity used : Nat)
    (physical : index.words.length < 2 ^ 64) (result : NatOperand)
    (success : (parent index base capacity used).result = .ok result) :
    result.words.length < 2 ^ 64 :=
  NatShift.shr_physical index 1 base capacity used result physical
    (arithmetic_success used _ result success)

theorem nextPow2_success_physical (count : NatOperand) (base capacity used : Nat)
    (physical : count.words.length < 2 ^ 64) (result : NatOperand)
    (success : (nextPow2 count base capacity used).result = .ok result) :
    result.words.length < 2 ^ 64 := by
  unfold nextPow2 at success
  split at success
  · cases success
    change 1 < 2 ^ 64
    decide
  · split at success
    · cases success
      exact physical
    · exact NatShift.shl_physical _ _ _ _ _ result (by change 1 < 2 ^ 64; decide)
        (arithmetic_success used _ result success)

theorem ceilShift_success_physical (value : NatOperand) (shift base capacity used : Nat)
    (physical : value.words.length < 2 ^ 64) (result : NatOperand)
    (success : (ceilShift value shift base capacity used).result = .ok result) :
    result.words.length < 2 ^ 64 := by
  unfold ceilShift at success
  split at success
  · exact NatShift.shr_physical _ _ _ _ _ result physical
      (arithmetic_success used _ result success)
  · split at success
    · cases success
    · cases success
      change 1 < 2 ^ 64
      decide
    · split at success
      · split at success
        · exact makeNatState_success_physical _ _ _ _ _ _ _ success
        · cases success
      · exact makeNatState_success_physical _ _ _ _ _ _ _ success

theorem parent_error (index : NatOperand) (base capacity used : Nat) (reason : Error)
    (failure : (parent index base capacity used).result = .error reason) : reason = scratch := by
  obtain ⟨source, observed, shape⟩ := arithmetic_error used _ reason failure
  rw [NatShift.shr_error index 1 base capacity used source observed] at shape
  exact shape

theorem nextPow2_error (count : NatOperand) (base capacity used : Nat) (reason : Error)
    (failure : (nextPow2 count base capacity used).result = .error reason) : reason = scratch := by
  unfold nextPow2 at failure
  split at failure
  · cases failure
  · split at failure
    · cases failure
    · obtain ⟨source, observed, shape⟩ := arithmetic_error used _ reason failure
      rw [NatShift.shl_error _ _ _ _ _ source observed] at shape
      exact shape

theorem ceilShift_error (value : NatOperand) (shift base capacity used : Nat) (reason : Error)
    (failure : (ceilShift value shift base capacity used).result = .error reason) : reason = scratch := by
  unfold ceilShift at failure
  split at failure
  · obtain ⟨source, observed, shape⟩ := arithmetic_error used _ reason failure
    rw [NatShift.shr_error _ _ _ _ _ source observed] at shape
    exact shape
  · split at failure
    · rename_i rejected checked
      cases failure
      exact wordCount_error _ _ checked
    · cases failure
    · split at failure
      · split at failure
        · exact makeNatState_error _ _ _ _ _ _ _ failure
        · cases failure
          rfl
      · exact makeNatState_error _ _ _ _ _ _ _ failure

theorem checkedDepth_error (index : NatOperand) (reason : Error)
    (failure : checkedDepth index = .error reason) : reason = .notAGindex index := by
  unfold checkedDepth at failure
  split at failure
  · cases failure
    rfl
  · cases failure

/-- Validation errors preserve their original raw operand, in the source's
outer-before-inner order; every remaining refusal is resource exhaustion. -/
theorem concat_error (outer inner : NatOperand) (base capacity used : Nat) (reason : Error)
    (failure : (concat outer inner base capacity used).result = .error reason) :
    reason = scratch ∨ reason = .notAGindex outer ∨ reason = .notAGindex inner := by
  unfold concat at failure
  split at failure
  · rename_i rejected checked
    cases failure
    exact Or.inr (Or.inl (checkedDepth_error _ _ checked))
  · split at failure
    · rename_i rejected checked
      cases failure
      exact Or.inr (Or.inr (checkedDepth_error _ _ checked))
    · split at failure
      · cases failure
      · split at failure
        · cases failure
        · split at failure
          · split at failure
            · rename_i rejected checked
              cases failure
              exact Or.inl (wordCount_error _ _ checked)
            · split at failure
              · exact Or.inl (makeNat_error _ _ _ _ _ _ failure)
              · cases failure
                exact Or.inl rfl
          · cases failure
            exact Or.inl rfl

end SszNative.Indices

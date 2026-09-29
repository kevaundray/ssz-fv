import SszIndicesArithmeticResources
import SszIndicesProgressive

set_option autoImplicit false

namespace SszNative.Indices

theorem makeNatState_success_physical {σ : Type} (words base capacity used : Nat) (state : σ)
    (fill : Nat → σ → BitVec 64 × σ) (result : NatOperand)
    (success : (makeNatState words base capacity used state fill).result = .ok result) :
    result.words.length < 2 ^ 64 := by
  cases words with
  | zero =>
      cases success
      change 1 < 2 ^ 64
      decide
  | succ words =>
      cases words with
      | zero =>
          cases success
          change 1 < 2 ^ 64
          decide
      | succ count =>
          cases reserved : Arena.reserve base capacity used (count + 2) with
          | none =>
              simp only [makeNatState, reserved, arithmetic, NatArithmetic.unchanged,
                Except.mapError] at success
              cases success
          | some reservation =>
              have checks := ((Arena.reserve_eq_some_iff_checks base capacity used
                (count + 2) (by omega) reservation).mp reserved).1
              simp only [makeNatState, reserved, arithmetic, Except.mapError,
                Except.ok.injEq] at success
              subst result
              simp only [NatOperand.words, fillWords_length]
              have bound := checks.1
              omega

theorem makeNat_success_physical (words base capacity used : Nat) (fill : Nat → BitVec 64)
    (result : NatOperand) (success : (makeNat words base capacity used fill).result = .ok result) :
    result.words.length < 2 ^ 64 :=
  makeNatState_success_physical words base capacity used () (fun i _ => (fill i, ())) result success

theorem shiftXor_success_physical (index : NatOperand) (shift : Nat) (flip : Bool)
    (base capacity used : Nat) (result : NatOperand)
    (success : (shiftXor index shift flip base capacity used).result = .ok result) :
    result.words.length < 2 ^ 64 := by
  unfold shiftXor at success
  split at success
  · cases success
  · exact makeNat_success_physical _ _ _ _ _ _ success

theorem below_success_physical (index : NatOperand) (bits base capacity used : Nat)
    (physical : index.words.length < 2 ^ 64) (result : NatOperand)
    (success : (below index bits base capacity used).result = .ok result) :
    result.words.length < 2 ^ 64 := by
  unfold below at success
  split at success
  · cases success
    exact physical
  · split at success
    · cases success
    · exact makeNat_success_physical _ _ _ _ _ _ success

theorem sibling_success_physical (index : NatOperand) (base capacity used : Nat)
    (result : NatOperand) (success : (sibling index base capacity used).result = .ok result) :
    result.words.length < 2 ^ 64 :=
  shiftXor_success_physical index 0 true base capacity used result success

theorem child_success_physical (index : NatOperand) (right : Bool) (base capacity used : Nat)
    (result : NatOperand) (success : (child index right base capacity used).result = .ok result) :
    result.words.length < 2 ^ 64 := by
  unfold child at success
  split at success
  · cases success
    change 1 < 2 ^ 64
    decide
  · split at success
    · split at success
      · cases success
      · exact makeNat_success_physical _ _ _ _ _ _ success
    · cases success

theorem concat_success_physical (outer inner : NatOperand) (base capacity used : Nat)
    (outerPhysical : outer.words.length < 2 ^ 64) (innerPhysical : inner.words.length < 2 ^ 64)
    (result : NatOperand) (success : (concat outer inner base capacity used).result = .ok result) :
    result.words.length < 2 ^ 64 := by
  unfold concat at success
  split at success
  · cases success
  · split at success
    · cases success
    · split at success
      · cases success
        exact outerPhysical
      · split at success
        · cases success
          exact innerPhysical
        · split at success
          · split at success
            · cases success
            · split at success
              · exact makeNat_success_physical _ _ _ _ _ _ success
              · cases success
          · cases success

theorem rebase_success_physical (index : NatOperand) (bits base capacity used : Nat)
    (result : NatOperand) (success : (rebase index bits base capacity used).result = .ok result) :
    result.words.length < 2 ^ 64 := by
  unfold rebase at success
  split at success
  · split at success
    · cases success
    · exact makeNat_success_physical _ _ _ _ _ _ success
  · cases success

theorem progressiveChunkIndex_success_physical (chunk : NatOperand) (base capacity used : Nat)
    (result : NatOperand) (success : (progressiveChunkIndex chunk base capacity used).result = .ok result) :
    result.words.length < 2 ^ 64 := by
  unfold progressiveChunkIndex at success
  dsimp only at success
  split at success
  · cases success
  · split at success
    · split at success
      · split at success
        · cases success
        · exact makeNatState_success_physical _ _ _ _ _ _ _ success
      · cases success
    · cases success

theorem wordCount_error (bits : Nat) (reason : Error)
    (failure : wordCount bits = .error reason) : reason = scratch := by
  by_cases checked : (bits / 64 + if bits % 64 = 0 then 0 else 1) < 2 ^ 64
  · simp only [wordCount, checked, ↓reduceIte] at failure
    cases failure
  · simp only [wordCount, checked, ↓reduceIte] at failure
    cases failure
    rfl

theorem makeNatState_error {σ : Type} (words base capacity used : Nat) (state : σ)
    (fill : Nat → σ → BitVec 64 × σ) (reason : Error)
    (failure : (makeNatState words base capacity used state fill).result = .error reason) :
    reason = scratch := by
  cases words with
  | zero => cases failure
  | succ words =>
      cases words with
      | zero => cases failure
      | succ count =>
          cases reserved : Arena.reserve base capacity used (count + 2) with
          | none =>
              simp only [makeNatState, reserved, arithmetic, NatArithmetic.unchanged,
                Except.mapError, Except.error.injEq] at failure
              exact failure.symm
          | some reservation =>
              simp only [makeNatState, reserved, arithmetic, Except.mapError] at failure
              cases failure

theorem makeNat_error (words base capacity used : Nat) (fill : Nat → BitVec 64)
    (reason : Error) (failure : (makeNat words base capacity used fill).result = .error reason) :
    reason = scratch :=
  makeNatState_error words base capacity used () (fun i _ => (fill i, ())) reason failure

theorem rebase_error (index : NatOperand) (bits base capacity used : Nat) (reason : Error)
    (failure : (rebase index bits base capacity used).result = .error reason) : reason = scratch := by
  unfold rebase at failure
  split at failure
  · split at failure
    · rename_i rejected checked
      cases failure
      exact wordCount_error _ _ checked
    · exact makeNat_error _ _ _ _ _ _ failure
  · cases failure
    rfl

theorem progressiveChunkIndex_error (chunk : NatOperand) (base capacity used : Nat)
    (reason : Error) (failure : (progressiveChunkIndex chunk base capacity used).result = .error reason) :
    reason = scratch := by
  unfold progressiveChunkIndex at failure
  dsimp only at failure
  split at failure
  · rename_i rejected checked
    cases failure
    exact wordCount_error _ _ checked
  · split at failure
    · split at failure
      · split at failure
        · rename_i rejected checked
          cases failure
          exact wordCount_error _ _ checked
        · exact makeNatState_error _ _ _ _ _ _ _ failure
      · cases failure
        rfl
    · cases failure
      rfl

end SszNative.Indices

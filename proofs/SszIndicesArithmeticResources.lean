import SszIndicesArithmetic

set_option autoImplicit false

namespace SszNative.Indices

theorem fillWords_length {σ : Type} (fill : Nat → σ → BitVec 64 × σ)
    (position count : Nat) (state : σ) :
    (fillWords fill position count state).1.length = count := by
  induction count generalizing position state with
  | zero => rfl
  | succ count ih =>
      simp only [fillWords, List.length_cons]
      rw [ih]

/-- Both pure and mutable initializers run exactly the reserved number of times. -/
theorem makeNatState_large {σ : Type} (count base capacity used : Nat) (state : σ)
    (fill : Nat → σ → BitVec 64 × σ) (reservation : Arena.Reservation)
    (reserved : Arena.reserve base capacity used (count + 2) = some reservation) :
    makeNatState (count + 2) base capacity used state fill =
      arithmetic used ⟨.ok (.large (BitVec.ofNat 64 reservation.pointer)
        (fillWords fill 0 (count + 2) state).1), reservation.used,
        some reservation, (fillWords fill 0 (count + 2) state).1⟩ := by
  simp only [makeNatState, reserved]

theorem makeNatState_exhausted {σ : Type} (count base capacity used : Nat) (state : σ)
    (fill : Nat → σ → BitVec 64 × σ)
    (reserved : Arena.reserve base capacity used (count + 2) = none) :
    makeNatState (count + 2) base capacity used state fill =
      arithmetic used (NatArithmetic.unchanged used (.error .scratchExhausted)) := by
  simp only [makeNatState, reserved]

def Atomic (used : Nat) (outcome : Outcome NatOperand) : Prop :=
  (outcome.effects = [] ∧ outcome.used = used) ∨
    ∃ child : NatArithmetic.Outcome NatOperand, outcome = arithmetic used child

theorem unchanged_atomic (used : Nat) (result : Except Error NatOperand) :
    Atomic used (unchanged used result) := Or.inl ⟨rfl, rfl⟩

theorem arithmetic_atomic (used : Nat) (child : NatArithmetic.Outcome NatOperand) :
    Atomic used (arithmetic used child) := Or.inr ⟨child, rfl⟩

theorem makeNatState_atomic {σ : Type} (words base capacity used : Nat) (state : σ)
    (fill : Nat → σ → BitVec 64 × σ) :
    Atomic used (makeNatState words base capacity used state fill) := by
  cases words with
  | zero => exact unchanged_atomic _ _
  | succ words =>
      cases words with
      | zero => exact unchanged_atomic _ _
      | succ count =>
          simp only [makeNatState]
          split <;> exact arithmetic_atomic _ _

theorem makeNatState_cursor_bounds {σ : Type} (words base capacity used : Nat) (state : σ)
    (fill : Nat → σ → BitVec 64 × σ) (valid : Arena.Valid base capacity used) :
    used ≤ (makeNatState words base capacity used state fill).used ∧
      (makeNatState words base capacity used state fill).used ≤ capacity := by
  cases words with
  | zero => exact ⟨Nat.le_refl _, valid.2.2.2⟩
  | succ words =>
      cases words with
      | zero => exact ⟨Nat.le_refl _, valid.2.2.2⟩
      | succ count =>
          cases reserved : Arena.reserve base capacity used (count + 2) with
          | none =>
              simp only [makeNatState, reserved, arithmetic, NatArithmetic.unchanged]
              exact ⟨Nat.le_refl _, valid.2.2.2⟩
          | some reservation =>
              have typed : TypedArena.reserve ⟨8, 3⟩ base capacity used (count + 2) =
                  some reservation := by rw [TypedArena.reserve_u64]; exact reserved
              simpa only [makeNatState, reserved, arithmetic] using
                TypedArena.reserve_cursor_bounds ⟨8, 3⟩ base capacity used (count + 2)
                  valid reservation typed

theorem makeNatState_used_mono {σ : Type} (words base capacity used : Nat) (state : σ)
    (fill : Nat → σ → BitVec 64 × σ) :
    used ≤ (makeNatState words base capacity used state fill).used := by
  cases words with
  | zero => exact Nat.le_refl _
  | succ words =>
      cases words with
      | zero => exact Nat.le_refl _
      | succ count =>
          cases reserved : Arena.reserve base capacity used (count + 2) with
          | none => simp only [makeNatState, reserved, arithmetic, NatArithmetic.unchanged, Nat.le_refl]
          | some reservation =>
              obtain ⟨_, shape⟩ := (Arena.reserve_eq_some_iff_checks base capacity used
                (count + 2) (by omega) reservation).mp reserved
              simp only [makeNatState, reserved, arithmetic]
              rw [shape]
              have := Arena.used_le_start base used
              simp only [Arena.finish]
              omega

theorem makeNat_cursor_bounds (words base capacity used : Nat) (fill : Nat → BitVec 64)
    (valid : Arena.Valid base capacity used) :
    used ≤ (makeNat words base capacity used fill).used ∧
      (makeNat words base capacity used fill).used ≤ capacity :=
  makeNatState_cursor_bounds words base capacity used () (fun i _ => (fill i, ())) valid

theorem makeNat_used_mono (words base capacity used : Nat) (fill : Nat → BitVec 64) :
    used ≤ (makeNat words base capacity used fill).used :=
  makeNatState_used_mono words base capacity used () (fun i _ => (fill i, ()))

theorem makeNat_atomic (words base capacity used : Nat) (fill : Nat → BitVec 64) :
    Atomic used (makeNat words base capacity used fill) :=
  makeNatState_atomic words base capacity used () (fun i _ => (fill i, ()))

theorem shiftXor_cursor_bounds (index : NatOperand) (shift : Nat) (flip : Bool)
    (base capacity used : Nat) (valid : Arena.Valid base capacity used) :
    used ≤ (shiftXor index shift flip base capacity used).used ∧
      (shiftXor index shift flip base capacity used).used ≤ capacity := by
  unfold shiftXor
  split
  · exact ⟨Nat.le_refl _, valid.2.2.2⟩
  · exact makeNat_cursor_bounds _ _ _ _ _ valid

theorem shiftXor_used_mono (index : NatOperand) (shift : Nat) (flip : Bool)
    (base capacity used : Nat) : used ≤ (shiftXor index shift flip base capacity used).used := by
  unfold shiftXor
  split
  · exact Nat.le_refl _
  · exact makeNat_used_mono _ _ _ _ _

theorem shiftXor_effects (index : NatOperand) (shift : Nat) (flip : Bool)
    (base capacity used : Nat) : Atomic used (shiftXor index shift flip base capacity used) := by
  unfold shiftXor
  split
  · exact unchanged_atomic _ _
  · exact makeNat_atomic _ _ _ _ _

/-- The initializer cannot fail: any failure is before the first limb write,
and no committed reservation is lost. -/
theorem makeNatState_error_cursor {σ : Type} (words base capacity used : Nat) (state : σ)
    (fill : Nat → σ → BitVec 64 × σ) (reason : Error)
    (failure : (makeNatState words base capacity used state fill).result = .error reason) :
    (makeNatState words base capacity used state fill).used = used := by
  cases words with
  | zero => cases failure
  | succ words =>
      cases words with
      | zero => cases failure
      | succ count =>
          cases reserved : Arena.reserve base capacity used (count + 2) with
          | none => simp only [makeNatState, reserved, arithmetic, NatArithmetic.unchanged]
          | some reservation =>
              simp only [makeNatState, reserved, arithmetic, Except.mapError] at failure
              cases failure

/-- A successful output describes exactly all written limbs, even redundant
high zeros; no hidden normalization or secondary allocation is introduced. -/
theorem makeNatState_success_value {σ : Type} (words base capacity used : Nat) (state : σ)
    (fill : Nat → σ → BitVec 64 × σ) (result : NatOperand)
    (success : (makeNatState words base capacity used state fill).result = .ok result) :
    result.value = Limbs.value (fillWords fill 0 words state).1 := by
  cases words with
  | zero =>
      cases success
      rfl
  | succ words =>
      cases words with
      | zero =>
          cases success
          simp [fillWords, NatOperand.value, NatOperand.words, Limbs.value]
      | succ count =>
          cases reserved : Arena.reserve base capacity used (count + 2) with
          | none =>
              simp only [makeNatState, reserved, arithmetic, NatArithmetic.unchanged,
                Except.mapError] at success
              cases success
          | some reservation =>
              simp only [makeNatState, reserved, arithmetic, Except.mapError,
                Except.ok.injEq] at success
              subst result
              rfl

end SszNative.Indices

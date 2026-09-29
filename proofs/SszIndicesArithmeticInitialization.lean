import SszIndicesArithmeticResources

set_option autoImplicit false

namespace SszNative.Indices

/-- Every prefix carries exactly the state used by the following initializer.
This includes ceil-shift carry and progressive subtraction borrow. -/
theorem fillWords_split {σ : Type} (fill : Nat → σ → BitVec 64 × σ)
    (position first rest : Nat) (state : σ) :
    fillWords fill position (first + rest) state =
      let initialized := fillWords fill position first state
      let suffix := fillWords fill (position + first) rest initialized.2
      (initialized.1 ++ suffix.1, suffix.2) := by
  induction first generalizing position state with
  | zero => simp [fillWords]
  | succ first ih =>
      simp only [Nat.succ_add, fillWords, ih, List.cons_append]
      simp only [Nat.add_comm, Nat.add_succ]

theorem fillWords_prefix {σ : Type} (fill : Nat → σ → BitVec 64 × σ)
    (position first rest : Nat) (state : σ) :
    (fillWords fill position (first + rest) state).1.take first =
      (fillWords fill position first state).1 := by
  rw [fillWords_split]
  have taken :
      ((fillWords fill position first state).1 ++
        (fillWords fill (position + first) rest (fillWords fill position first state).2).1).take
          (fillWords fill position first state).1.length =
        (fillWords fill position first state).1 := List.take_left
  simpa only [fillWords_length] using taken

/-- Every written prefix lies in the one committed reservation; no arithmetic
on its logical value or representation normalization is used for this frame. -/
theorem makeNatState_slot_within (count base capacity used : Nat)
    (reservation : Arena.Reservation)
    (reserved : Arena.reserve base capacity used (count + 2) = some reservation)
    (slot : Nat) (inside : slot < count + 2) :
    base + used ≤ reservation.pointer + 8 * slot ∧
      reservation.pointer + 8 * slot + 8 ≤ base + reservation.used ∧
      reservation.used ≤ capacity := by
  obtain ⟨checks, shape⟩ := (Arena.reserve_eq_some_iff_checks base capacity used
    (count + 2) (by omega) reservation).mp reserved
  rw [shape]
  have start := Arena.used_le_start base used
  have bound := checks.2.2.2.2.2
  simp only [Arena.finish] at bound ⊢
  omega

/-- The event stores the complete initialized list, and its length is the
reservation count, including zero high limbs retained by make_nat. -/
theorem makeNatState_initialized {σ : Type} (count base capacity used : Nat) (state : σ)
    (fill : Nat → σ → BitVec 64 × σ) (reservation : Arena.Reservation)
    (reserved : Arena.reserve base capacity used (count + 2) = some reservation) :
    ∃ child : NatArithmetic.Outcome NatOperand,
      (makeNatState (count + 2) base capacity used state fill).effects = [.arithmetic used child] ∧
      child.allocation = some reservation ∧ child.written.length = count + 2 ∧
      child.used = reservation.used := by
  rw [makeNatState_large count base capacity used state fill reservation reserved]
  refine ⟨_, rfl, rfl, ?_, rfl⟩
  exact fillWords_length fill 0 (count + 2) state

end SszNative.Indices

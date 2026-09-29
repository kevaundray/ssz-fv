import SszIndicesFrontierResourcesCore
import SszIndicesArithmeticResources
import SszNatShiftResources

set_option autoImplicit false

namespace SszNative.Indices

/-- Cursor replay of the recorded events. Arithmetic events retain the complete
native arithmetic outcome, including allocation failure and written limbs. -/
inductive FrontierTrace (base capacity : Nat) : Nat → List Effect → Nat → Prop where
  | nil (used : Nat) : FrontierTrace base capacity used [] used
  | arithmetic (used : Nat) (child : NatArithmetic.Outcome NatOperand)
      {rest : List Effect} {final : Nat}
      (tail : FrontierTrace base capacity child.used rest final) :
      FrontierTrace base capacity used (.arithmetic used child :: rest) final
  | reserveFailure (layout : TypedArena.Layout) (count used : Nat)
      (failed : TypedArena.reserve layout base capacity used count = none)
      {rest : List Effect} {final : Nat}
      (tail : FrontierTrace base capacity used rest final) :
      FrontierTrace base capacity used (.reserve layout count used none :: rest) final
  | reserveSuccess (layout : TypedArena.Layout) (count used : Nat)
      (reservation : Arena.Reservation)
      (reserved : TypedArena.reserve layout base capacity used count = some reservation)
      {rest : List Effect} {final : Nat}
      (tail : FrontierTrace base capacity reservation.used rest final) :
      FrontierTrace base capacity used (.reserve layout count used (some reservation) :: rest) final
  | initialized (pointer slot used : Nat) (value : NatOperand)
      {rest : List Effect} {final : Nat} (tail : FrontierTrace base capacity used rest final) :
      FrontierTrace base capacity used (.initialized pointer slot value :: rest) final
  | sorted (pointer used : Nat) (values : List NatOperand)
      {rest : List Effect} {final : Nat} (tail : FrontierTrace base capacity used rest final) :
      FrontierTrace base capacity used (.sorted pointer values :: rest) final

theorem FrontierTrace.append {base capacity initial middle final : Nat}
    {first second : List Effect}
    (before : FrontierTrace base capacity initial first middle)
    (after : FrontierTrace base capacity middle second final) :
    FrontierTrace base capacity initial (first ++ second) final := by
  induction before with
  | nil used => simpa only [List.nil_append] using after
  | arithmetic used child tail ih => exact .arithmetic used child (ih after)
  | reserveFailure layout count used failed tail ih =>
    exact .reserveFailure layout count used failed (ih after)
  | reserveSuccess layout count used reservation reserved tail ih =>
    exact .reserveSuccess layout count used reservation reserved (ih after)
  | initialized pointer slot used value tail ih =>
    exact .initialized pointer slot used value (ih after)
  | sorted pointer used values tail ih => exact .sorted pointer used values (ih after)

theorem bind_frontierTrace {α β : Type} (base capacity used : Nat)
    (first : Outcome α) (next : α → Nat → Outcome β)
    (before : FrontierTrace base capacity used first.effects first.used)
    (after : ∀ value cursor,
      FrontierTrace base capacity cursor (next value cursor).effects (next value cursor).used) :
    FrontierTrace base capacity used (bind first next).effects (bind first next).used := by
  cases returned : first.result with
  | error reason => simpa only [bind, returned] using before
  | ok value => simpa only [bind, returned] using before.append (after value first.used)

/-- Initializer bodies cannot reserve another Nat array or sort/initialize the
outer array. Their only possible event is their own arithmetic allocation. -/
def ArithmeticEffects (effects : List Effect) : Prop :=
  ∀ effect ∈ effects, ∃ initial child, effect = .arithmetic initial child

theorem Atomic.arithmeticEffects {used : Nat} {outcome : Outcome NatOperand}
    (atomic : Atomic used outcome) : ArithmeticEffects outcome.effects := by
  rcases atomic with ⟨empty, _⟩ | ⟨child, same⟩
  · simp [ArithmeticEffects, empty]
  · subst outcome
    intro effect member
    have same : effect = .arithmetic used child := by simpa [arithmetic] using member
    exact ⟨used, child, same⟩

theorem Atomic.trace {base capacity used : Nat} {outcome : Outcome NatOperand}
    (atomic : Atomic used outcome) : FrontierTrace base capacity used outcome.effects outcome.used := by
  rcases atomic with ⟨empty, cursor⟩ | ⟨child, same⟩
  · rw [empty, cursor]
    exact .nil used
  · subst outcome
    exact .arithmetic used child (.nil child.used)

/-- A reusable valid-arena cursor invariant, including the error branch. -/
def FrontierCursor (_base capacity initial final : Nat) : Prop :=
  initial ≤ final ∧ final ≤ capacity

theorem bind_cursor_bounds {α β : Type} (base capacity used : Nat)
    (valid : Arena.Valid base capacity used) (first : Outcome α)
    (next : α → Nat → Outcome β)
    (firstSafe : FrontierCursor base capacity used first.used)
    (nextSafe : ∀ value cursor, Arena.Valid base capacity cursor →
      FrontierCursor base capacity cursor (next value cursor).used) :
    FrontierCursor base capacity used (bind first next).used := by
  cases returned : first.result with
  | error reason => simpa only [bind, returned] using firstSafe
  | ok value =>
    have validNext : Arena.Valid base capacity first.used :=
      ⟨valid.1, valid.2.1, valid.2.2.1, firstSafe.2⟩
    have second := nextSafe value first.used validNext
    simpa only [bind, returned] using
      (show FrontierCursor base capacity used (next value first.used).used from
        ⟨Nat.le_trans firstSafe.1 second.1, second.2⟩)

theorem fillLevels_cursor_bounds (reservation : Arena.Reservation) (keepCandidate : Nat → Bool)
    (make : Nat → Nat → Outcome NatOperand) (base capacity : Nat)
    (safe : ∀ level cursor, Arena.Valid base capacity cursor →
      FrontierCursor base capacity cursor (make level cursor).used)
    (remaining level slot used : Nat) (valid : Arena.Valid base capacity used) :
    FrontierCursor base capacity used
      (fillLevels reservation keepCandidate make remaining level slot used).used := by
  induction remaining generalizing level slot used with
  | zero => exact ⟨Nat.le_refl _, valid.2.2.2⟩
  | succ remaining ih =>
    simp only [fillLevels]
    split
    · apply bind_cursor_bounds base capacity used valid _ _ (safe level used valid)
      intro value cursor cursorValid
      apply bind_cursor_bounds base capacity cursor cursorValid _ _
        ⟨Nat.le_refl _, cursorValid.2.2.2⟩
      intro accepted cursor cursorValid
      apply bind_cursor_bounds base capacity cursor cursorValid _ _
        (ih (level + 1) (slot + 1) cursor cursorValid)
      intro result cursor cursorValid
      exact ⟨Nat.le_refl _, cursorValid.2.2.2⟩
    · exact ih (level + 1) slot used valid

theorem fillClaims_cursor_bounds (indices : List NatOperand) (helpers : Bool)
    (reservation : Arena.Reservation) (base capacity : Nat)
    (remaining : List NatOperand) (claim slot used : Nat)
    (valid : Arena.Valid base capacity used) :
    FrontierCursor base capacity used
      (fillClaims indices helpers reservation base capacity remaining claim slot used).used := by
  induction remaining generalizing claim slot used with
  | nil => exact ⟨Nat.le_refl _, valid.2.2.2⟩
  | cons index rest ih =>
    unfold fillClaims
    apply bind_cursor_bounds base capacity used valid
    · apply fillLevels_cursor_bounds
      · intro level cursor cursorValid
        cases helpers
        · exact NatShift.shr_cursor_bounds index level base capacity cursor cursorValid
        · exact shiftXor_cursor_bounds index level true base capacity cursor cursorValid
      · exact valid
    · intro first cursor cursorValid
      apply bind_cursor_bounds base capacity cursor cursorValid _ _
        (ih (claim + 1) first.2 cursor cursorValid)
      intro second cursor cursorValid
      exact ⟨Nat.le_refl _, cursorValid.2.2.2⟩

theorem reserveNats_cursor_bounds (count base capacity used : Nat)
    (valid : Arena.Valid base capacity used) :
    FrontierCursor base capacity used (reserveNats count base capacity used).used := by
  cases reserved : TypedArena.reserve natLayout base capacity used count with
  | none => exact ⟨by simp [reserveNats, reserved], by simpa [reserveNats, reserved] using valid.2.2.2⟩
  | some reservation =>
    simpa only [reserveNats, reserved, FrontierCursor] using
      TypedArena.reserve_cursor_bounds natLayout base capacity used count valid reservation reserved

theorem reserveNats_zero (base capacity used : Nat) :
    reserveNats 0 base capacity used =
      ⟨.ok ⟨8, used⟩, used, [.reserve natLayout 0 used (some ⟨8, used⟩)]⟩ := by
  simp only [reserveNats, TypedArena.reserve_zero, natLayout, TypedArena.Layout.alignment,
    Nat.reducePow]

theorem reserveNats_exhausted (count base capacity used : Nat)
    (failed : TypedArena.reserve natLayout base capacity used count = none) :
    reserveNats count base capacity used =
      ⟨.error scratch, used, [.reserve natLayout count used none]⟩ := by
  simp only [reserveNats, failed]

/-- The exact 16-byte outer frame is committed before any child allocation.
Zero-count frames deliberately have no address/capacity side condition. -/
theorem reserveNats_frame (count base capacity used : Nat) (reservation : Arena.Reservation)
    (reserved : TypedArena.reserve natLayout base capacity used count = some reservation) :
    (count = 0 ∧ reservation = ⟨8, used⟩) ∨
    (0 < count ∧ TypedArena.Checks natLayout base capacity used count ∧
      reservation.pointer = base + TypedArena.start natLayout base used ∧
      reservation.used = TypedArena.finish natLayout base used count ∧
      reservation.pointer + 16 * count = base + reservation.used ∧ used ≤ reservation.used) := by
  by_cases zero : count = 0
  · subst count
    have same : (⟨8, used⟩ : Arena.Reservation) = reservation := by
      simpa only [TypedArena.reserve_zero, natLayout, TypedArena.Layout.alignment,
        Nat.reducePow, Option.some.injEq] using reserved
    exact Or.inl ⟨rfl, same.symm⟩
  · rw [TypedArena.reserve_positive natLayout base capacity used count
      (Nat.pos_of_ne_zero zero) (by decide)] at reserved
    split at reserved
    · rename_i checks
      cases reserved
      refine Or.inr ⟨Nat.pos_of_ne_zero zero, checks, rfl, rfl, ?_, ?_⟩
      · simp only [TypedArena.finish, natLayout, Nat.add_assoc]
      · exact TypedArena.used_le_finish natLayout base used count
    · cases reserved

/-- No initializer can write a different array or outside the selected slot
interval. This statement includes partial failure, not only successful fills. -/
def FrontierWrites (reservation : Arena.Reservation) (slot count : Nat) (effects : List Effect) : Prop :=
  ∀ pointer position value, Effect.initialized pointer position value ∈ effects →
    pointer = reservation.pointer ∧ slot ≤ position ∧ position < slot + count

theorem fillLevels_writes (reservation : Arena.Reservation) (keepCandidate : Nat → Bool)
    (make : Nat → Nat → Outcome NatOperand)
    (atomic : ∀ level cursor, ArithmeticEffects (make level cursor).effects)
    (remaining level slot used : Nat) :
    FrontierWrites reservation slot (retainedLevels keepCandidate remaining level)
      (fillLevels reservation keepCandidate make remaining level slot used).effects := by
  induction remaining generalizing level slot used with
  | zero => simp [FrontierWrites, fillLevels, unchanged]
  | succ remaining ih =>
    by_cases selected : keepCandidate level = true
    · cases returned : (make level used).result with
      | error reason =>
        intro pointer position value member
        have inner : Effect.initialized pointer position value ∈ (make level used).effects := by
          simpa only [fillLevels, selected, ↓reduceIte, bind, returned] using member
        obtain ⟨initial, child, impossible⟩ := atomic level used _ inner
        cases impossible
      | ok value =>
        intro pointer position written member
        have splitMember : Effect.initialized pointer position written ∈ (make level used).effects ∨
            Effect.initialized pointer position written = .initialized reservation.pointer slot value ∨
            Effect.initialized pointer position written ∈
              (fillLevels reservation keepCandidate make remaining (level + 1) (slot + 1)
                (make level used).used).effects := by
          cases suffix : (fillLevels reservation keepCandidate make remaining (level + 1) (slot + 1)
              (make level used).used).result <;>
            simpa [fillLevels, selected, bind, returned, suffix, unchanged,
              List.mem_append, or_assoc] using member
        rcases splitMember with inner | same | later
        · obtain ⟨initial, child, impossible⟩ := atomic level used _ inner
          cases impossible
        · cases same
          refine ⟨rfl, Nat.le_refl _, ?_⟩
          simp only [retainedLevels, selected, ↓reduceIte]
          omega
        · obtain ⟨pointerEq, lower, upper⟩ := ih (level + 1) (slot + 1)
            (make level used).used pointer position written later
          simp only [retainedLevels, selected, ↓reduceIte]
          exact ⟨pointerEq, by omega, by omega⟩
    · have excluded : keepCandidate level = false := Bool.eq_false_iff.mpr selected
      simpa only [fillLevels, excluded, Bool.false_eq_true, ↓reduceIte,
        retainedLevels, Nat.zero_add] using ih (level + 1) slot used

end SszNative.Indices

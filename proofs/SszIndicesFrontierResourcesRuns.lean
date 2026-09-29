import SszIndicesFrontierResourcesTrace

set_option autoImplicit false

namespace SszNative.Indices

theorem fillLevels_trace (reservation : Arena.Reservation) (keepCandidate : Nat → Bool)
    (make : Nat → Nat → Outcome NatOperand) (base capacity : Nat)
    (atomic : ∀ level cursor, Atomic cursor (make level cursor))
    (remaining level slot used : Nat) :
    FrontierTrace base capacity used
      (fillLevels reservation keepCandidate make remaining level slot used).effects
      (fillLevels reservation keepCandidate make remaining level slot used).used := by
  induction remaining generalizing level slot used with
  | zero => exact .nil used
  | succ remaining ih =>
    simp only [fillLevels]
    split
    · apply bind_frontierTrace base capacity used _ _ (atomic level used).trace
      intro value cursor
      apply bind_frontierTrace base capacity cursor _ _
        (.initialized reservation.pointer slot cursor value (.nil cursor))
      intro accepted cursor
      apply bind_frontierTrace base capacity cursor _ _ (ih (level + 1) (slot + 1) cursor)
      intro result cursor
      exact .nil cursor
    · exact ih (level + 1) slot used

theorem fillClaims_trace (indices : List NatOperand) (helpers : Bool)
    (reservation : Arena.Reservation) (base capacity : Nat)
    (remaining : List NatOperand) (claim slot used : Nat) :
    FrontierTrace base capacity used
      (fillClaims indices helpers reservation base capacity remaining claim slot used).effects
      (fillClaims indices helpers reservation base capacity remaining claim slot used).used := by
  induction remaining generalizing claim slot used with
  | nil => exact .nil used
  | cons index rest ih =>
    unfold fillClaims
    apply bind_frontierTrace base capacity used
    · apply fillLevels_trace
      intro level cursor
      cases helpers
      · exact arithmetic_atomic _ _
      · exact shiftXor_effects _ _ _ _ _ _
    · intro first cursor
      apply bind_frontierTrace base capacity cursor _ _ (ih (claim + 1) first.2 cursor)
      intro second cursor
      exact .nil cursor

theorem reserveNats_trace (count base capacity used : Nat) :
    FrontierTrace base capacity used (reserveNats count base capacity used).effects
      (reserveNats count base capacity used).used := by
  cases reserved : TypedArena.reserve natLayout base capacity used count with
  | none =>
    simpa only [reserveNats, reserved] using
      FrontierTrace.reserveFailure natLayout count used reserved (.nil used)
  | some reservation =>
    simpa only [reserveNats, reserved] using
      FrontierTrace.reserveSuccess natLayout count used reservation reserved (.nil reservation.used)

theorem pathIndices_trace (index : NatOperand) (base capacity used : Nat) :
    FrontierTrace base capacity used (pathIndices index base capacity used).effects
      (pathIndices index base capacity used).used := by
  unfold pathIndices
  apply bind_frontierTrace base capacity used _ _ (.nil used)
  intro count cursor
  split
  · exact .nil cursor
  · apply bind_frontierTrace base capacity cursor _ _ (reserveNats_trace count base capacity cursor)
    intro reservation cursor
    apply bind_frontierTrace base capacity cursor
    · apply fillLevels_trace
      intro level cursor
      exact arithmetic_atomic _ _
    · intro result cursor
      exact .nil cursor

theorem branchIndices_trace (index : NatOperand) (base capacity used : Nat) :
    FrontierTrace base capacity used (branchIndices index base capacity used).effects
      (branchIndices index base capacity used).used := by
  unfold branchIndices
  apply bind_frontierTrace base capacity used _ _ (.nil used)
  intro count cursor
  split
  · exact .nil cursor
  · apply bind_frontierTrace base capacity cursor _ _ (reserveNats_trace count base capacity cursor)
    intro reservation cursor
    apply bind_frontierTrace base capacity cursor
    · apply fillLevels_trace
      intro level cursor
      exact shiftXor_effects _ _ _ _ _ _
    · intro result cursor
      exact .nil cursor

theorem collectPathIndices_trace (indices : List NatOperand) (base capacity used : Nat) :
    FrontierTrace base capacity used (collectPathIndices indices base capacity used).effects
      (collectPathIndices indices base capacity used).used := by
  unfold collectPathIndices
  apply bind_frontierTrace base capacity used _ _ (.nil used)
  intro count cursor
  apply bind_frontierTrace base capacity cursor _ _ (reserveNats_trace count base capacity cursor)
  intro reservation cursor
  apply bind_frontierTrace base capacity cursor _ _
    (fillClaims_trace indices false reservation base capacity indices 0 0 cursor)
  intro result cursor
  exact .nil cursor

theorem helperIndices_trace (indices : List NatOperand) (base capacity used : Nat) :
    FrontierTrace base capacity used (helperIndices indices base capacity used).effects
      (helperIndices indices base capacity used).used := by
  unfold helperIndices
  apply bind_frontierTrace base capacity used _ _ (.nil used)
  intro accepted cursor
  apply bind_frontierTrace base capacity cursor _ _ (.nil cursor)
  intro count cursor
  apply bind_frontierTrace base capacity cursor _ _ (reserveNats_trace count base capacity cursor)
  intro reservation cursor
  apply bind_frontierTrace base capacity cursor _ _
    (fillClaims_trace indices true reservation base capacity indices 0 0 cursor)
  intro result cursor
  exact .sorted reservation.pointer cursor _ (.nil cursor)

theorem pathIndices_cursor_bounds (index : NatOperand) (base capacity used : Nat)
    (valid : Arena.Valid base capacity used) :
    FrontierCursor base capacity used (pathIndices index base capacity used).used := by
  unfold pathIndices
  apply bind_cursor_bounds base capacity used valid _ _ ⟨Nat.le_refl _, valid.2.2.2⟩
  intro count cursor cursorValid
  split
  · exact ⟨Nat.le_refl _, cursorValid.2.2.2⟩
  · apply bind_cursor_bounds base capacity cursor cursorValid _ _
      (reserveNats_cursor_bounds count base capacity cursor cursorValid)
    intro reservation cursor cursorValid
    apply bind_cursor_bounds base capacity cursor cursorValid
    · apply fillLevels_cursor_bounds
      · intro level cursor cursorValid
        exact NatShift.shr_cursor_bounds index level base capacity cursor cursorValid
      · exact cursorValid
    · intro result cursor cursorValid
      exact ⟨Nat.le_refl _, cursorValid.2.2.2⟩

theorem branchIndices_cursor_bounds (index : NatOperand) (base capacity used : Nat)
    (valid : Arena.Valid base capacity used) :
    FrontierCursor base capacity used (branchIndices index base capacity used).used := by
  unfold branchIndices
  apply bind_cursor_bounds base capacity used valid _ _ ⟨Nat.le_refl _, valid.2.2.2⟩
  intro count cursor cursorValid
  split
  · exact ⟨Nat.le_refl _, cursorValid.2.2.2⟩
  · apply bind_cursor_bounds base capacity cursor cursorValid _ _
      (reserveNats_cursor_bounds count base capacity cursor cursorValid)
    intro reservation cursor cursorValid
    apply bind_cursor_bounds base capacity cursor cursorValid
    · apply fillLevels_cursor_bounds
      · intro level cursor cursorValid
        exact shiftXor_cursor_bounds index level true base capacity cursor cursorValid
      · exact cursorValid
    · intro result cursor cursorValid
      exact ⟨Nat.le_refl _, cursorValid.2.2.2⟩

theorem collectPathIndices_cursor_bounds (indices : List NatOperand) (base capacity used : Nat)
    (valid : Arena.Valid base capacity used) :
    FrontierCursor base capacity used (collectPathIndices indices base capacity used).used := by
  unfold collectPathIndices
  apply bind_cursor_bounds base capacity used valid _ _ ⟨Nat.le_refl _, valid.2.2.2⟩
  intro count cursor cursorValid
  apply bind_cursor_bounds base capacity cursor cursorValid _ _
    (reserveNats_cursor_bounds count base capacity cursor cursorValid)
  intro reservation cursor cursorValid
  apply bind_cursor_bounds base capacity cursor cursorValid _ _
    (fillClaims_cursor_bounds indices false reservation base capacity indices 0 0 cursor cursorValid)
  intro result cursor cursorValid
  exact ⟨Nat.le_refl _, cursorValid.2.2.2⟩

theorem helperIndices_cursor_bounds (indices : List NatOperand) (base capacity used : Nat)
    (valid : Arena.Valid base capacity used) :
    FrontierCursor base capacity used (helperIndices indices base capacity used).used := by
  unfold helperIndices
  apply bind_cursor_bounds base capacity used valid _ _ ⟨Nat.le_refl _, valid.2.2.2⟩
  intro accepted cursor cursorValid
  apply bind_cursor_bounds base capacity cursor cursorValid _ _ ⟨Nat.le_refl _, cursorValid.2.2.2⟩
  intro count cursor cursorValid
  apply bind_cursor_bounds base capacity cursor cursorValid _ _
    (reserveNats_cursor_bounds count base capacity cursor cursorValid)
  intro reservation cursor cursorValid
  apply bind_cursor_bounds base capacity cursor cursorValid _ _
    (fillClaims_cursor_bounds indices true reservation base capacity indices 0 0 cursor cursorValid)
  intro result cursor cursorValid
  exact ⟨Nat.le_refl _, cursorValid.2.2.2⟩

theorem fillClaims_writes (indices : List NatOperand) (helpers : Bool)
    (reservation : Arena.Reservation) (base capacity : Nat)
    (remaining : List NatOperand) (claim slot used : Nat) :
    FrontierWrites reservation slot (retainedClaims indices helpers remaining claim)
      (fillClaims indices helpers reservation base capacity remaining claim slot used).effects := by
  induction remaining generalizing claim slot used with
  | nil => simp [FrontierWrites, fillClaims, unchanged]
  | cons index rest ih =>
    let keepCandidate := if helpers then isHelper indices index claim else fun _ => true
    let make := if helpers then fun level cursor => shiftXor index level true base capacity cursor
      else fun level cursor => arithmetic cursor (NatShift.shr index level base capacity cursor)
    let first := fillLevels reservation keepCandidate make (depth index) 0 slot used
    have firstWrites : FrontierWrites reservation slot (retainedLevels keepCandidate (depth index) 0)
        first.effects := by
      apply fillLevels_writes
      intro level cursor
      cases helpers
      · exact (arithmetic_atomic _ _).arithmeticEffects
      · exact (shiftXor_effects _ _ _ _ _ _).arithmeticEffects
    cases returned : first.result with
    | error reason =>
      intro pointer position value member
      have firstMember : Effect.initialized pointer position value ∈ first.effects := by
        change Effect.initialized pointer position value ∈
          (bind first fun values cursor =>
            bind (fillClaims indices helpers reservation base capacity rest (claim + 1) values.2 cursor)
              fun second cursor => unchanged cursor (.ok (values.1 ++ second.1, second.2))).effects at member
        simpa only [bind, returned] using member
      obtain ⟨pointerEq, lower, upper⟩ := firstWrites pointer position value firstMember
      exact ⟨pointerEq, lower, by simp only [retainedClaims]; dsimp [keepCandidate] at upper; omega⟩
    | ok pair =>
      have slotEq := ((fillLevels_prefix reservation keepCandidate make (depth index) 0 slot used).success
        pair.1 pair.2 returned).2.1
      intro pointer position value member
      have splitMember : Effect.initialized pointer position value ∈ first.effects ∨
          Effect.initialized pointer position value ∈
            (fillClaims indices helpers reservation base capacity rest (claim + 1) pair.2 first.used).effects := by
        change Effect.initialized pointer position value ∈
          (bind first fun values cursor =>
            bind (fillClaims indices helpers reservation base capacity rest (claim + 1) values.2 cursor)
              fun second cursor => unchanged cursor (.ok (values.1 ++ second.1, second.2))).effects at member
        cases suffix : (fillClaims indices helpers reservation base capacity rest
            (claim + 1) pair.2 first.used).result <;>
          simpa only [bind, returned, suffix, unchanged, List.append_nil, List.mem_append] using member
      rcases splitMember with firstMember | restMember
      · obtain ⟨pointerEq, lower, upper⟩ := firstWrites pointer position value firstMember
        exact ⟨pointerEq, lower, by simp only [retainedClaims]; dsimp [keepCandidate] at upper; omega⟩
      · obtain ⟨pointerEq, lower, upper⟩ := ih (claim + 1) pair.2 first.used
          pointer position value restMember
        exact ⟨pointerEq, by omega, by simp only [retainedClaims]; dsimp [keepCandidate] at slotEq; omega⟩

end SszNative.Indices

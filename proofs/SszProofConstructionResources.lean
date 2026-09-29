import SszProofConstruction
import SszProofTraversalResources
import SszIndicesFrontierResourcesRuns

set_option autoImplicit false

namespace SszNative.Proof

def initializedPrefix (pointer : Nat) : Nat → List Ssz.Bytes → List (Nat × Nat × Ssz.Bytes)
  | _, [] => []
  | position, root :: rest => (pointer, position, root) :: initializedPrefix pointer (position + 1) rest

theorem TraversalTrace.hashWrites {arena : Delimited.ArenaState} {effects : List Effect}
    {used : Nat} (trace : TraversalTrace arena effects used) : hashWrites effects = [] := by
  induction trace with
  | nil arena => rfl
  | layout arena outcome ran rest used later ih => exact ih

theorem nodeRoot_hashWrites (desc : Codec.Desc) (value : Codec.Value) (index : NatOperand)
    (arena : Delimited.ArenaState) : hashWrites (nodeRoot desc value index arena).effects = [] :=
  (nodeRoot_trace desc value index arena).hashWrites

/-- An error retains exactly a consecutive completed prefix of the reserved
hash slots, not a fictitious wholly initialized output or a rolled-back frame. -/
theorem fillHashRoots_initialized_prefix (desc : Codec.Desc) (value : Codec.Value)
    (reservation : Arena.Reservation) (indices : List NatOperand) (position : Nat)
    (arena : Delimited.ArenaState) :
    ∃ completed, completed.length ≤ indices.length ∧
      hashWrites (fillHashRoots desc value reservation indices position arena).effects =
        initializedPrefix reservation.pointer position completed := by
  induction indices generalizing position arena with
  | nil => exact ⟨[], Nat.le_refl _, rfl⟩
  | cons index rest ih =>
      have noWrites := nodeRoot_hashWrites desc value index arena
      cases rooted : (nodeRoot desc value index arena).result with
      | error reason =>
          refine ⟨[], by simp, ?_⟩
          simpa only [fillHashRoots, bind, rooted, initializedPrefix] using noWrites
      | ok root =>
          obtain ⟨completed, bounded, written⟩ := ih (position + 1)
            { arena with used := (nodeRoot desc value index arena).used }
          refine ⟨root :: completed, by simpa only [List.length_cons] using Nat.succ_le_succ bounded, ?_⟩
          cases filled : (fillHashRoots desc value reservation rest (position + 1)
              { arena with used := (nodeRoot desc value index arena).used }).result <;>
            simp only [fillHashRoots, bind, rooted, filled, unchanged, List.nil_append,
              List.append_nil, List.cons_append, hashWrites_append, noWrites, hashWrites,
              initializedPrefix, written]

/-- Successful construction writes every output slot exactly once in helper
order; byte payloads in the trace equal the returned hashes positionally. -/
theorem fillHashRoots_success_prefix (desc : Codec.Desc) (value : Codec.Value)
    (reservation : Arena.Reservation) (indices : List NatOperand) (position : Nat)
    (arena : Delimited.ArenaState) (roots : List Ssz.Bytes)
    (success : (fillHashRoots desc value reservation indices position arena).result = .ok roots) :
    roots.length = indices.length ∧
      hashWrites (fillHashRoots desc value reservation indices position arena).effects =
        initializedPrefix reservation.pointer position roots := by
  induction indices generalizing position arena roots with
  | nil => cases success; exact ⟨rfl, rfl⟩
  | cons index rest ih =>
      have noWrites := nodeRoot_hashWrites desc value index arena
      cases rooted : (nodeRoot desc value index arena).result with
      | error reason => simp only [fillHashRoots, bind, rooted] at success; cases success
      | ok root =>
          cases filled : (fillHashRoots desc value reservation rest (position + 1)
              { arena with used := (nodeRoot desc value index arena).used }).result with
          | error reason =>
              simp only [fillHashRoots, bind, rooted, filled] at success
              cases success
          | ok later =>
              have next := ih (position + 1)
                { arena with used := (nodeRoot desc value index arena).used } later filled
              simp only [fillHashRoots, bind, rooted, filled, unchanged, Except.ok.injEq] at success
              subst roots
              constructor
              · simpa only [List.length_cons] using congrArg Nat.succ next.1
              · simp only [fillHashRoots, bind, rooted, filled, unchanged, List.nil_append,
                  List.append_nil, List.cons_append, hashWrites_append, noWrites, hashWrites,
                  initializedPrefix, next.2]

/-- Each event replays an actual child trace or an exact typed reservation.
Initialized events denote only semantic Hash cells, never surrounding padding. -/
inductive ConstructionTrace : Delimited.ArenaState → List Effect → Nat → Prop where
  | nil (arena : Delimited.ArenaState) : ConstructionTrace arena [] arena.used
  | layout (arena : Delimited.ArenaState) (outcome : HashLayout.Outcome Unit)
      (ran : HashLayout.Trace arena outcome.effects outcome.used)
      {rest : List Effect} {used : Nat}
      (later : ConstructionTrace { arena with used := outcome.used } rest used) :
      ConstructionTrace arena (.layout arena outcome :: rest) used
  | indices (arena : Delimited.ArenaState) (outcome : Indices.Outcome Unit)
      (ran : Indices.FrontierTrace arena.base arena.capacity arena.used outcome.effects outcome.used)
      (safe : Arena.Valid arena.base arena.capacity arena.used →
        Indices.FrontierCursor arena.base arena.capacity arena.used outcome.used)
      {rest : List Effect} {used : Nat}
      (later : ConstructionTrace { arena with used := outcome.used } rest used) :
      ConstructionTrace arena (.indices arena outcome :: rest) used
  | reserveFailure (layout : TypedArena.Layout) (arena : Delimited.ArenaState) (count : Nat)
      (failed : TypedArena.reserve layout arena.base arena.capacity arena.used count = none)
      {rest : List Effect} {used : Nat} (later : ConstructionTrace arena rest used) :
      ConstructionTrace arena (.reserve layout arena count none :: rest) used
  | reserveSuccess (layout : TypedArena.Layout) (arena : Delimited.ArenaState) (count : Nat)
      (reservation : Arena.Reservation)
      (reserved : TypedArena.reserve layout arena.base arena.capacity arena.used count = some reservation)
      {rest : List Effect} {used : Nat}
      (later : ConstructionTrace { arena with used := reservation.used } rest used) :
      ConstructionTrace arena (.reserve layout arena count (some reservation) :: rest) used
  | initialized (arena : Delimited.ArenaState) (pointer position : Nat) (bytes : Ssz.Bytes)
      {rest : List Effect} {used : Nat} (later : ConstructionTrace arena rest used) :
      ConstructionTrace arena (.initialized pointer position bytes :: rest) used

theorem TraversalTrace.construction {arena : Delimited.ArenaState} {effects : List Effect}
    {used : Nat} (trace : TraversalTrace arena effects used) : ConstructionTrace arena effects used := by
  induction trace with
  | nil arena => exact .nil arena
  | layout arena outcome ran rest used later ih => exact .layout arena outcome ran ih

theorem ConstructionTrace.append {arena : Delimited.ArenaState} {first second : List Effect}
    {middle used : Nat} (before : ConstructionTrace arena first middle)
    (after : ConstructionTrace { arena with used := middle } second used) :
    ConstructionTrace arena (first ++ second) used := by
  induction before with
  | nil arena => exact after
  | layout arena outcome ran later ih => exact .layout arena outcome ran (ih after)
  | indices arena outcome ran safe later ih => exact .indices arena outcome ran safe (ih after)
  | reserveFailure layout arena count failed later ih =>
      exact .reserveFailure layout arena count failed (ih after)
  | reserveSuccess layout arena count reservation reserved later ih =>
      exact .reserveSuccess layout arena count reservation reserved (ih after)
  | initialized arena pointer position bytes later ih =>
      exact .initialized arena pointer position bytes (ih after)

theorem bind_constructionTrace {α β : Type} (arena : Delimited.ArenaState)
    (first : Outcome α) (next : α → Nat → Outcome β)
    (before : ConstructionTrace arena first.effects first.used)
    (after : ∀ value used, ConstructionTrace { arena with used := used }
      (next value used).effects (next value used).used) :
    ConstructionTrace arena (bind first next).effects (bind first next).used := by
  cases result : first.result with
  | error reason => simpa only [bind, result] using before
  | ok value => simpa only [bind, result] using before.append (after value first.used)

theorem fillHashRoots_trace (desc : Codec.Desc) (value : Codec.Value)
    (reservation : Arena.Reservation) (indices : List NatOperand) (position : Nat)
    (arena : Delimited.ArenaState) :
    ConstructionTrace arena (fillHashRoots desc value reservation indices position arena).effects
      (fillHashRoots desc value reservation indices position arena).used := by
  induction indices generalizing position arena with
  | nil => exact .nil arena
  | cons index rest ih =>
      simp only [fillHashRoots]
      apply bind_constructionTrace _ _ _ (nodeRoot_trace desc value index arena).construction
      intro root used
      apply bind_constructionTrace _ _ _
        (.initialized { arena with used := used } reservation.pointer position root (.nil _))
      intro _ used'
      apply bind_constructionTrace _ _ _ (ih (position + 1) { arena with used := used' })
      intro roots used''
      exact .nil _

theorem reserveHashRoots_trace (desc : Codec.Desc) (value : Codec.Value)
    (indices : List NatOperand) (arena : Delimited.ArenaState) :
    ConstructionTrace arena (reserveHashRoots desc value indices arena).effects
      (reserveHashRoots desc value indices arena).used := by
  unfold reserveHashRoots
  split
  · rename_i failed
    exact .reserveFailure hashLayout arena indices.length failed (.nil arena)
  · rename_i reservation reserved
    exact .reserveSuccess hashLayout arena indices.length reservation reserved
      (fillHashRoots_trace desc value reservation indices 0 { arena with used := reservation.used })

theorem buildProof_trace (desc : Codec.Desc) (value : Codec.Value) (index : NatOperand)
    (arena : Delimited.ArenaState) :
    ConstructionTrace arena (buildProof desc value index arena).effects
      (buildProof desc value index arena).used := by
  unfold buildProof
  apply bind_constructionTrace
  · exact .indices arena _ (Indices.branchIndices_trace index arena.base arena.capacity arena.used)
      (Indices.branchIndices_cursor_bounds index arena.base arena.capacity arena.used) (.nil _)
  · intro branches used
    exact reserveHashRoots_trace desc value branches.values { arena with used := used }

theorem buildMultiproof_trace (desc : Codec.Desc) (value : Codec.Value) (indices : List NatOperand)
    (arena : Delimited.ArenaState) :
    ConstructionTrace arena (buildMultiproof desc value indices arena).effects
      (buildMultiproof desc value indices arena).used := by
  unfold buildMultiproof
  apply bind_constructionTrace
  · exact .indices arena _ (Indices.helperIndices_trace indices arena.base arena.capacity arena.used)
      (Indices.helperIndices_cursor_bounds indices arena.base arena.capacity arena.used) (.nil _)
  · intro helpers used
    exact reserveHashRoots_trace desc value helpers.values { arena with used := used }

theorem ConstructionTrace.cursor_bounds {arena : Delimited.ArenaState}
    {effects : List Effect} {used : Nat} (trace : ConstructionTrace arena effects used)
    (valid : Arena.Valid arena.base arena.capacity arena.used) :
    arena.used ≤ used ∧ used ≤ arena.capacity := by
  induction trace with
  | nil arena => exact ⟨Nat.le_refl _, valid.2.2.2⟩
  | layout arena outcome ran later ih =>
      have first := ran.cursorSafe
      have last := ih (first.2 valid)
      exact ⟨Nat.le_trans first.1 last.1, last.2⟩
  | indices arena outcome ran safe later ih =>
      have first := safe valid
      have last := ih ⟨valid.1, valid.2.1, valid.2.2.1, first.2⟩
      exact ⟨Nat.le_trans first.1 last.1, last.2⟩
  | reserveFailure layout arena count failed later ih => exact ih valid
  | reserveSuccess layout arena count reservation reserved later ih =>
      have first := TypedArena.reserve_cursor_bounds layout arena.base arena.capacity arena.used
        count valid reservation reserved
      have last := ih ⟨valid.1, valid.2.1, valid.2.2.1, first.2⟩
      exact ⟨Nat.le_trans first.1 last.1, last.2⟩
  | initialized arena pointer position bytes later ih => exact ih valid

theorem buildProof_cursor_bounds (desc : Codec.Desc) (value : Codec.Value)
    (index : NatOperand) (arena : Delimited.ArenaState)
    (valid : Arena.Valid arena.base arena.capacity arena.used) :
    arena.used ≤ (buildProof desc value index arena).used ∧
      (buildProof desc value index arena).used ≤ arena.capacity :=
  (buildProof_trace desc value index arena).cursor_bounds valid

theorem buildMultiproof_cursor_bounds (desc : Codec.Desc) (value : Codec.Value)
    (indices : List NatOperand) (arena : Delimited.ArenaState)
    (valid : Arena.Valid arena.base arena.capacity arena.used) :
    arena.used ≤ (buildMultiproof desc value indices arena).used ∧
      (buildMultiproof desc value indices arena).used ≤ arena.capacity :=
  (buildMultiproof_trace desc value indices arena).cursor_bounds valid

/-- Hash alignment is one, so no output padding can precede its byte cells.
Zero-count returns the specified dangling pointer without touching the cursor. -/
theorem reserveHashRoots_frame (count : Nat) (arena : Delimited.ArenaState)
    (reservation : Arena.Reservation)
    (reserved : TypedArena.reserve hashLayout arena.base arena.capacity arena.used count =
      some reservation) :
    (count = 0 ∧ reservation = ⟨1, arena.used⟩) ∨
      (0 < count ∧ reservation.pointer = arena.base + arena.used ∧
        reservation.used = arena.used + 32 * count ∧
        TypedArena.Checks hashLayout arena.base arena.capacity arena.used count) := by
  by_cases zero : count = 0
  · subst count
    simp only [TypedArena.reserve_zero, hashLayout, TypedArena.Layout.alignment,
      Nat.pow_zero, Option.some.injEq] at reserved
    exact Or.inl ⟨rfl, reserved.symm⟩
  · rw [TypedArena.reserve_positive hashLayout arena.base arena.capacity arena.used count
      (Nat.pos_of_ne_zero zero) (by decide)] at reserved
    split at reserved
    · rename_i checked
      cases reserved
      refine Or.inr ⟨Nat.pos_of_ne_zero zero, ?_, ?_, checked⟩ <;>
        simp [TypedArena.start, TypedArena.padding, TypedArena.aligned,
          TypedArena.finish, TypedArena.Layout.alignment, hashLayout]
    · cases reserved

end SszNative.Proof

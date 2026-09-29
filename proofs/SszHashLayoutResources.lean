import SszHashLayoutRoot
import SszHashLayoutArithmeticResources

set_option autoImplicit false

namespace SszNative.HashLayout

open Codec (Desc Value)

theorem sequence_trace (element : Desc) (values : List Value) (positions : Option NatOperand)
    (mixin : Option Ssz.Bytes) (arena : Delimited.ArenaState) :
    Trace arena (sequence element values positions mixin arena).effects
      (sequence element values positions mixin arena).used := by
  unfold sequence
  apply bind_trace _ _ _ (unchanged_trace arena _)
  intro width used
  cases width with
  | none => exact unchanged_trace { arena with used := used } _
  | some width =>
    apply bind_trace _ _ _ (unchanged_trace { arena with used := used } _)
    intro checked used'
    cases positions with
    | none => exact unchanged_trace { arena with used := used' } _
    | some count =>
      apply bind_trace _ _ _ (mul_trace _ _ _)
      intro bytes used''
      apply bind_trace _ _ _ (ceilDiv_trace _ _ _)
      intro limit used'''
      exact unchanged_trace { arena with used := used''' } _

/-- Every raw layout branch has a complete arithmetic trace, including count
construction on semantic errors. No width, physical-slice, or scratch premise
is required for this resource theorem. -/
theorem layout_trace (desc : Desc) (value : Value) (arena : Delimited.ArenaState) :
    Trace arena (layout desc value arena).effects (layout desc value arena).used := by
  cases desc with
  | primitive shape =>
    cases shape <;> cases value <;> simp only [layout]
    repeat' (first
      | exact unchanged_trace _ _
      | exact ceilDiv_trace _ _ _
      | exact fromWide_trace _ _
      | apply bind_trace
      | (intro)
      | split)
  | vector element length =>
    cases value <;> simp only [layout]
    repeat' (first
      | exact unchanged_trace _ _
      | exact sequence_trace _ _ _ _ _
      | split)
  | list element length =>
    cases value <;> simp only [layout]
    repeat' (first
      | exact unchanged_trace _ _
      | exact sequence_trace _ _ _ _ _
      | split)
  | progressiveList element length =>
    cases value <;> simp only [layout]
    repeat' (first
      | exact unchanged_trace _ _
      | exact sequence_trace _ _ _ _ _
      | split)
  | container fields =>
    cases value <;> simp only [layout]
    repeat' (first
      | exact unchanged_trace _ _
      | split)
  | progressiveContainer active fields =>
    cases value <;> simp only [layout]
    repeat' (first
      | exact unchanged_trace _ _
      | split)
  | compatibleUnion options =>
    cases value <;> simp only [layout]
    repeat' (first
      | exact unchanged_trace _ _
      | split)

/-- Recursive visitors are required only at an actually selected child. This
is a compositional rule, not an assumption of future root success. -/
theorem leafRoot_trace (view : Layout) (index : Nat) (arena : Delimited.ArenaState)
    (visit : (desc : Desc) → (value : Value) →
      view.nested index = some (desc, value) → Delimited.ArenaState → Outcome Ssz.Bytes)
    (visits : ∀ desc value selected cursor,
      Trace cursor (visit desc value selected cursor).effects
        (visit desc value selected cursor).used) :
    Trace arena (leafRoot view index arena visit).effects (leafRoot view index arena visit).used := by
  unfold leafRoot
  split
  · split
    · exact unchanged_trace arena _
    · split
      · exact unchanged_trace arena _
      · exact visits _ _ _ arena
  · exact unchanged_trace arena _

/-- Pushing and finishing the finite accumulator allocate no Nat scratch. Every
visited leaf, even a rejecting one, contributes exactly its own ordered trace. -/
theorem stream_trace (leaf : Nat → Delimited.ArenaState → Outcome Ssz.Bytes)
    (visits : ∀ index arena, Trace arena (leaf index arena).effects (leaf index arena).used)
    (remaining index : Nat) (tree : TreeState) (arena : Delimited.ArenaState) :
    Trace arena (stream leaf remaining index tree arena).effects
      (stream leaf remaining index tree arena).used := by
  induction remaining generalizing index tree arena with
  | zero => exact unchanged_trace arena _
  | succ remaining ih =>
    simp only [stream]
    apply bind_trace _ _ _ (visits index arena)
    intro node used
    apply bind_trace _ _ _ (unchanged_trace { arena with used := used } _)
    intro next used'
    exact ih (index + 1) next { arena with used := used' }

theorem rootStep_trace (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (visit : Visit value)
    (visits : ∀ child member childDesc cursor,
      Trace cursor (visit child member childDesc cursor).effects
        (visit child member childDesc cursor).used) :
    Trace arena (rootStep desc value arena visit).effects (rootStep desc value arena visit).used := by
  have planned := layout_trace desc value arena
  simp only [rootStep]
  split
  · exact planned
  · rename_i view success
    apply Trace.append planned
    apply bind_trace
    · apply stream_trace
      intro index cursor
      apply leafRoot_trace
      intro childDesc child selected childArena
      exact visits _ _ _ _
    · intro root used
      exact unchanged_trace { arena with used := used } _

/-- Structural child descent closes the visitor premise. All finite raw values
are covered, without a caller-supplied fuel bound or any future-execution fact. -/
theorem hashTreeRoot_trace (desc : Desc) (value : Value) (arena : Delimited.ArenaState) :
    Trace arena (hashTreeRoot desc value arena).effects (hashTreeRoot desc value arena).used := by
  rw [hashTreeRoot]
  apply rootStep_trace
  intro child member childDesc childArena
  exact hashTreeRoot_trace childDesc child childArena
termination_by value.nesting
decreasing_by exact Value.child_nesting_lt _ _ (by assumption)

theorem indexedRoot_trace (view : Layout) (index : Nat) (arena : Delimited.ArenaState) :
    Trace arena (indexedRoot view index arena).effects (indexedRoot view index arena).used := by
  apply leafRoot_trace
  intro desc value selected cursor
  exact hashTreeRoot_trace desc value cursor

theorem sequence_cursorSafe (element : Desc) (values : List Value) (positions : Option NatOperand)
    (mixin : Option Ssz.Bytes) (arena : Delimited.ArenaState) :
    CursorSafe arena (sequence element values positions mixin arena).used :=
  (sequence_trace element values positions mixin arena).cursorSafe

theorem layout_cursorSafe (desc : Desc) (value : Value) (arena : Delimited.ArenaState) :
    CursorSafe arena (layout desc value arena).used := (layout_trace desc value arena).cursorSafe

theorem leafRoot_cursorSafe (view : Layout) (index : Nat) (arena : Delimited.ArenaState)
    (visit : (desc : Desc) → (value : Value) →
      view.nested index = some (desc, value) → Delimited.ArenaState → Outcome Ssz.Bytes)
    (visits : ∀ desc value selected cursor,
      Trace cursor (visit desc value selected cursor).effects
        (visit desc value selected cursor).used) :
    CursorSafe arena (leafRoot view index arena visit).used :=
  (leafRoot_trace view index arena visit visits).cursorSafe

theorem rootStep_cursorSafe (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (visit : Visit value)
    (visits : ∀ child member childDesc cursor,
      Trace cursor (visit child member childDesc cursor).effects
        (visit child member childDesc cursor).used) :
    CursorSafe arena (rootStep desc value arena visit).used :=
  (rootStep_trace desc value arena visit visits).cursorSafe

theorem hashTreeRoot_cursorSafe (desc : Desc) (value : Value) (arena : Delimited.ArenaState) :
    CursorSafe arena (hashTreeRoot desc value arena).used :=
  (hashTreeRoot_trace desc value arena).cursorSafe

theorem indexedRoot_cursorSafe (view : Layout) (index : Nat) (arena : Delimited.ArenaState) :
    CursorSafe arena (indexedRoot view index arena).used :=
  (indexedRoot_trace view index arena).cursorSafe

theorem hashTreeRoot_used_mono (desc : Desc) (value : Value) (arena : Delimited.ArenaState) :
    arena.used ≤ (hashTreeRoot desc value arena).used := (hashTreeRoot_cursorSafe desc value arena).1

theorem hashTreeRoot_valid (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (valid : Arena.Valid arena.base arena.capacity arena.used) :
    Arena.Valid arena.base arena.capacity (hashTreeRoot desc value arena).used :=
  (hashTreeRoot_cursorSafe desc value arena).2 valid

end SszNative.HashLayout

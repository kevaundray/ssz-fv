import SszHashLayoutArithmeticProofs
import SszCodecMeasureResourcesCore

set_option autoImplicit false

namespace SszNative.HashLayout

/-- Reuse the accepted arena invariant, including monotonicity on invalid arenas. -/
abbrev CursorSafe := CodecMeasure.CursorSafe

theorem cursorSafe_refl (arena : Delimited.ArenaState) : CursorSafe arena arena.used :=
  CodecMeasure.cursorSafe_refl arena

theorem cursorSafe_trans (arena : Delimited.ArenaState) (middle used : Nat)
    (first : CursorSafe arena middle)
    (second : CursorSafe { arena with used := middle } used) : CursorSafe arena used :=
  CodecMeasure.cursorSafe_trans arena middle used first second

theorem unchanged_cursorSafe {α : Type} (arena : Delimited.ArenaState)
    (result : Except Error α) : CursorSafe arena (unchanged arena.used result).used :=
  cursorSafe_refl arena

theorem bind_cursorSafe {α β : Type} (arena : Delimited.ArenaState)
    (first : Outcome α) (next : α → Nat → Outcome β)
    (safeFirst : CursorSafe arena first.used)
    (safeNext : ∀ value used, CursorSafe { arena with used := used } (next value used).used) :
    CursorSafe arena (bind first next).used := by
  cases result : first.result with
  | error reason => simpa only [bind, result] using safeFirst
  | ok value =>
    simpa only [bind, result] using
      cursorSafe_trans arena first.used _ safeFirst (safeNext value first.used)

theorem fromWide_cursorSafe (wide : BitVec 128) (arena : Delimited.ArenaState) :
    CursorSafe arena (fromWide wide arena).used := by
  unfold fromWide NatArithmetic.fromWide
  split
  · exact cursorSafe_refl arena
  · split
    · exact cursorSafe_refl arena
    · rename_i reservation reserved
      exact CodecMeasure.reserve_cursorSafe arena 2 reservation reserved

theorem add_cursorSafe (left right : NatOperand) (arena : Delimited.ArenaState) :
    CursorSafe arena (add left right arena).used :=
  CodecMeasure.add_cursorSafe left right arena

theorem mul_cursorSafe (left right : NatOperand) (arena : Delimited.ArenaState) :
    CursorSafe arena (mul left right arena).used := by
  change CursorSafe arena (NatMul.run left right arena.base arena.capacity arena.used).used
  cases allocated : (NatMul.run left right arena.base arena.capacity arena.used).allocation with
  | none =>
    rw [(NatMul.no_allocation_resources _ _ _ _ _ allocated).1]
    exact cursorSafe_refl arena
  | some reservation =>
    obtain ⟨same, _, reserved⟩ := NatMul.allocation_exact _ _ _ _ _ reservation allocated
    rw [same]
    exact CodecMeasure.reserve_cursorSafe arena _ reservation reserved

theorem divide_cursorSafe (operand : NatOperand) (divisor : BitVec 64)
    (arena : Delimited.ArenaState) : CursorSafe arena (divide operand divisor arena).used := by
  change CursorSafe arena (NatDivision.run operand divisor arena.base arena.capacity arena.used).used
  cases allocated : (NatDivision.run operand divisor arena.base arena.capacity arena.used).allocation with
  | none =>
    rw [(NatDivision.no_allocation_resources _ _ _ _ _ allocated).1]
    exact cursorSafe_refl arena
  | some reservation =>
    obtain ⟨cursor, _, checks, _, geometry, _⟩ :=
      NatDivision.allocation_resources _ _ _ _ _ reservation allocated
    have positive : 0 < (if operand.wordCount ≤ 2 then 2 else operand.wordCount) := by
      split <;> omega
    have reserved : Arena.reserve arena.base arena.capacity arena.used
        (if operand.wordCount ≤ 2 then 2 else operand.wordCount) =
        some ⟨arena.base + Arena.start arena.base arena.used, reservation.used⟩ := by
      apply (Arena.reserve_eq_some_iff_checks _ _ _ _ positive _).mpr
      exact ⟨checks, by simp only [geometry]⟩
    rw [cursor]
    exact CodecMeasure.reserve_cursorSafe arena _
      ⟨arena.base + Arena.start arena.base arena.used, reservation.used⟩ reserved

theorem ceilDiv_cursorSafe (operand : NatOperand) (divisor : BitVec 64)
    (arena : Delimited.ArenaState) : CursorSafe arena (ceilDiv operand divisor arena).used := by
  apply bind_cursorSafe _ _ _ (divide_cursorSafe operand divisor arena)
  intro pair used
  split
  · exact cursorSafe_refl { arena with used := used }
  · exact add_cursorSafe _ _ _

/-- One exact native arithmetic attempt. These constructors require the entire
accepted outcome, not merely an equal represented value or a matching cursor. -/
inductive EffectRun : Delimited.ArenaState → Effect → Nat → Prop where
  | fromWide (wide : BitVec 128) (arena : Delimited.ArenaState) :
      EffectRun arena
        (.fromWide wide arena (NatArithmetic.fromWide arena.base arena.capacity arena.used wide))
        (NatArithmetic.fromWide arena.base arena.capacity arena.used wide).used
  | add (left right : NatOperand) (arena : Delimited.ArenaState) :
      EffectRun arena (.add left right arena (NatAdd.run left right arena.base arena.capacity arena.used))
        (NatAdd.run left right arena.base arena.capacity arena.used).used
  | mul (left right : NatOperand) (arena : Delimited.ArenaState) :
      EffectRun arena (.mul left right arena (NatMul.run left right arena.base arena.capacity arena.used))
        (NatMul.run left right arena.base arena.capacity arena.used).used
  | divide (operand : NatOperand) (divisor : BitVec 64) (arena : Delimited.ArenaState) :
      EffectRun arena
        (.divide operand divisor arena (NatDivision.run operand divisor arena.base arena.capacity arena.used))
        (NatDivision.run operand divisor arena.base arena.capacity arena.used).used

/-- The actual resource trace threads each committed cursor into the next
attempt, preserving original metadata and every failed attempt. -/
inductive Trace : Delimited.ArenaState → List Effect → Nat → Prop where
  | nil (arena : Delimited.ArenaState) : Trace arena [] arena.used
  | cons {arena : Delimited.ArenaState} {effect : Effect} {middle final : Nat}
      {rest : List Effect} (step : EffectRun arena effect middle)
      (following : Trace { arena with used := middle } rest final) :
      Trace arena (effect :: rest) final

theorem EffectRun.cursorSafe {arena : Delimited.ArenaState} {effect : Effect} {used : Nat}
    (step : EffectRun arena effect used) : CursorSafe arena used := by
  cases step with
  | fromWide wide arena => exact fromWide_cursorSafe wide arena
  | add left right arena => exact add_cursorSafe left right arena
  | mul left right arena => exact mul_cursorSafe left right arena
  | divide operand divisor arena => exact divide_cursorSafe operand divisor arena

theorem Trace.cursorSafe {arena : Delimited.ArenaState} {effects : List Effect} {used : Nat}
    (trace : Trace arena effects used) : CursorSafe arena used := by
  induction trace with
  | nil arena => exact cursorSafe_refl arena
  | cons step following ih => exact cursorSafe_trans _ _ _ step.cursorSafe ih

theorem Trace.append {arena : Delimited.ArenaState} {first second : List Effect}
    {middle used : Nat} (before : Trace arena first middle)
    (after : Trace { arena with used := middle } second used) :
    Trace arena (first ++ second) used := by
  induction before with
  | nil arena => simpa only [List.nil_append] using after
  | cons step following ih => exact .cons step (ih after)

theorem unchanged_trace {α : Type} (arena : Delimited.ArenaState) (result : Except Error α) :
    Trace arena (unchanged arena.used result).effects (unchanged arena.used result).used :=
  .nil arena

theorem fromWide_trace (wide : BitVec 128) (arena : Delimited.ArenaState) :
    Trace arena (fromWide wide arena).effects (fromWide wide arena).used :=
  .cons (.fromWide wide arena) (.nil _)

theorem add_trace (left right : NatOperand) (arena : Delimited.ArenaState) :
    Trace arena (add left right arena).effects (add left right arena).used :=
  .cons (.add left right arena) (.nil _)

theorem mul_trace (left right : NatOperand) (arena : Delimited.ArenaState) :
    Trace arena (mul left right arena).effects (mul left right arena).used :=
  .cons (.mul left right arena) (.nil _)

theorem divide_trace (operand : NatOperand) (divisor : BitVec 64) (arena : Delimited.ArenaState) :
    Trace arena (divide operand divisor arena).effects (divide operand divisor arena).used :=
  .cons (.divide operand divisor arena) (.nil _)

theorem bind_trace {α β : Type} (arena : Delimited.ArenaState) (first : Outcome α)
    (next : α → Nat → Outcome β) (before : Trace arena first.effects first.used)
    (after : ∀ value used, Trace { arena with used := used }
      (next value used).effects (next value used).used) :
    Trace arena (bind first next).effects (bind first next).used := by
  cases result : first.result with
  | error reason => simpa only [bind, result] using before
  | ok value => simpa only [bind, result] using before.append (after value first.used)

theorem ceilDiv_trace (operand : NatOperand) (divisor : BitVec 64)
    (arena : Delimited.ArenaState) :
    Trace arena (ceilDiv operand divisor arena).effects (ceilDiv operand divisor arena).used := by
  apply bind_trace _ _ _ (divide_trace operand divisor arena)
  intro pair used
  split
  · exact unchanged_trace { arena with used := used } _
  · exact add_trace _ _ _

/-- Bind never erases a prefix, including when either stage fails. -/
theorem bind_effects_prefix {α β : Type} (first : Outcome α) (next : α → Nat → Outcome β) :
    ∃ suffix, (bind first next).effects = first.effects ++ suffix := by
  cases result : first.result with
  | error reason => exact ⟨[], by simp only [bind, result, List.append_nil]⟩
  | ok value => exact ⟨(next value first.used).effects, by simp only [bind, result]⟩

/-- General result reasoning composes without a premise about future execution. -/
def Ensures {α : Type} (post : α → Prop) (outcome : Outcome α) : Prop :=
  ∀ value, outcome.result = .ok value → post value

theorem bind_ensures {α β : Type} (first : Outcome α) (next : α → Nat → Outcome β)
    (middle : α → Prop) (post : β → Prop) (before : Ensures middle first)
    (after : ∀ value used, middle value → Ensures post (next value used)) :
    Ensures post (bind first next) := by
  intro result success
  cases initial : first.result with
  | error reason => simp only [bind, initial] at success; cases success
  | ok value =>
    exact after value first.used (before value initial) result
      (by simpa only [bind, initial] using success)

end SszNative.HashLayout

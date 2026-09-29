import SszX86.CodecMeasureFixedArithmeticGeometry
import SszX86.CodecMeasureFixedArithmeticBounds
import SszFixedSizeResources

namespace SszX86.CodecMeasureFixed
open SszNative

/-- Physical geometry of the existing ordered arithmetic trace. -/
structure TraceGeometry {α : Type} (arena : Delimited.ArenaState)
    (outcome : Serialize.Outcome α) : Prop where
  lower : arena.used ≤ outcome.used
  upper : outcome.used ≤ arena.capacity
  writes : ∀ a, Measure.AllocationWrites outcome.calls a →
    arena.base + arena.used ≤ a.toNat ∧ a.toNat < arena.base + outcome.used

theorem unchanged_trace_geometry {α : Type} (arena : Delimited.ArenaState)
    (result : Except Serialize.Error α) (bound : arena.used ≤ arena.capacity) :
    TraceGeometry arena (Serialize.unchanged arena.used result) := by
  refine ⟨Nat.le_refl _, bound, ?_⟩
  intro a writes
  obtain ⟨call, member, rest⟩ := writes
  cases member

theorem bind_trace_geometry {α β : Type} (arena : Delimited.ArenaState)
    (first : Serialize.Outcome α) (next : α → Nat → Serialize.Outcome β)
    (initial : TraceGeometry arena first)
    (following : ∀ value used, used ≤ arena.capacity →
      TraceGeometry {arena with used := used} (next value used)) :
    TraceGeometry arena (Serialize.bind first next) := by
  cases result : first.result with
  | error reason =>
    simp only [Serialize.bind, result]
    exact ⟨initial.lower, initial.upper, initial.writes⟩
  | ok value =>
    have later := following value first.used initial.upper
    simp only [Serialize.bind, result]
    refine ⟨Nat.le_trans initial.lower later.lower, later.upper, ?_⟩
    intro a writes
    obtain ⟨call, member, reservation, allocated, span⟩ := writes
    rcases List.mem_append.mp member with before | after
    · have bounds := initial.writes a ⟨call, before, reservation, allocated, span⟩
      exact ⟨bounds.1, by have := later.lower; dsimp only at this; omega⟩
    · have bounds := later.writes a ⟨call, after, reservation, allocated, span⟩
      exact ⟨by have := initial.lower; dsimp only at bounds; omega, bounds.2⟩

theorem add_trace_geometry (left right : NatOperand) (arena : Delimited.ArenaState)
    (arenaBound : arena.base + arena.capacity ≤ 2 ^ 64)
    (bound : arena.used ≤ arena.capacity) : TraceGeometry arena (FixedSize.add left right arena) := by
  have cursor := add_cursor_bounds left right arena.base arena.capacity arena.used bound
  refine ⟨cursor.1, cursor.2, ?_⟩
  intro a writes
  have written := (arithmeticWrites_singleton
    (SszNative.NatAdd.run left right arena.base arena.capacity arena.used) a).2 writes
  have geometry := add_writes_geometry left right arena.base arena.capacity arena.used arenaBound a written
  exact ⟨geometry.1, geometry.2.1⟩

theorem mul_trace_geometry (left right : NatOperand) (arena : Delimited.ArenaState)
    (arenaBound : arena.base + arena.capacity ≤ 2 ^ 64)
    (bound : arena.used ≤ arena.capacity) : TraceGeometry arena (FixedSize.mul left right arena) := by
  have cursor := mul_used_bounds left right arena.base arena.capacity arena.used bound
  refine ⟨cursor.1, cursor.2, ?_⟩
  intro a writes
  have written := (arithmeticWrites_singleton
    (SszNative.NatMul.run left right arena.base arena.capacity arena.used) a).2 writes
  have geometry := mul_writes_geometry left right arena.base arena.capacity arena.used arenaBound a written
  exact ⟨geometry.1, geometry.2.1⟩

theorem div8_trace_geometry (operand : NatOperand) (arena : Delimited.ArenaState)
    (arenaBound : arena.base + arena.capacity ≤ 2 ^ 64)
    (bound : arena.used ≤ arena.capacity) : TraceGeometry arena (FixedSize.div8 operand arena) := by
  have cursor := divide8_cursor_bounds operand arena.base arena.capacity arena.used bound
  refine ⟨cursor.1, cursor.2, ?_⟩
  intro a writes
  have written := (arithmeticWrites_singleton (FixedSize.divisionCall
    (SszNative.NatDivision.run operand 8 arena.base arena.capacity arena.used)) a).2 writes
  have geometry := divide8_writes_geometry operand arena.base arena.capacity arena.used arenaBound a written
  exact ⟨geometry.1, geometry.2.1⟩

theorem bitWidth_trace_geometry (operand : NatOperand) (arena : Delimited.ArenaState)
    (arenaBound : arena.base + arena.capacity ≤ 2 ^ 64)
    (bound : arena.used ≤ arena.capacity) : TraceGeometry arena (FixedSize.bitWidth operand arena) := by
  unfold FixedSize.bitWidth
  apply bind_trace_geometry _ _ _ (div8_trace_geometry operand arena arenaBound bound)
  intro divided used usedBound
  split
  · exact unchanged_trace_geometry _ _ usedBound
  · exact add_trace_geometry _ _ _ arenaBound usedBound

theorem primitive_trace_geometry (shape : Serialize.Desc) (arena : Delimited.ArenaState)
    (arenaBound : arena.base + arena.capacity ≤ 2 ^ 64)
    (bound : arena.used ≤ arena.capacity) : TraceGeometry arena (FixedSize.measurePrimitive shape arena) := by
  cases shape with
  | bitVector length =>
    unfold FixedSize.measurePrimitive
    apply bind_trace_geometry _ _ _ (bitWidth_trace_geometry length arena arenaBound bound)
    intro width used usedBound
    exact unchanged_trace_geometry _ _ usedBound
  | _ => exact unchanged_trace_geometry _ _ bound

end SszX86.CodecMeasureFixed

import SszX86.CodecMeasureFixedArithmeticTraceGeometryCore

namespace SszX86.CodecMeasureFixed
open SszNative

mutual
  theorem measureFixed_trace_geometry (desc : SszNative.Codec.Desc) (arena : Delimited.ArenaState)
      (arenaBound : arena.base + arena.capacity ≤ 2 ^ 64)
      (bound : arena.used ≤ arena.capacity) :
      TraceGeometry arena (FixedSize.measureFixed desc arena) := by
    cases desc with
    | primitive shape => exact primitive_trace_geometry shape arena arenaBound bound
    | vector element length =>
      simp only [FixedSize.measureFixed]
      apply bind_trace_geometry _ _ _ (measureFixed_trace_geometry element arena arenaBound bound)
      intro measured used usedBound
      cases measured with
      | none => exact unchanged_trace_geometry _ _ usedBound
      | some width =>
        apply bind_trace_geometry _ _ _
          (mul_trace_geometry width length {arena with used := used} arenaBound usedBound)
        intro total final finalBound
        exact unchanged_trace_geometry _ _ finalBound
    | container fields => exact measureFields_trace_geometry fields (.small 0) arena arenaBound bound
    | progressiveContainer active fields =>
      exact measureFields_trace_geometry fields (.small 0) arena arenaBound bound
    | _ => exact unchanged_trace_geometry _ _ bound

  theorem measureFields_trace_geometry (fields : List (String × SszNative.Codec.Desc))
      (total : NatOperand) (arena : Delimited.ArenaState)
      (arenaBound : arena.base + arena.capacity ≤ 2 ^ 64)
      (bound : arena.used ≤ arena.capacity) :
      TraceGeometry arena (FixedSize.measureFields fields total arena) := by
    cases fields with
    | nil => exact unchanged_trace_geometry _ _ bound
    | cons field rest =>
      rcases field with ⟨name, shape⟩
      simp only [FixedSize.measureFields]
      apply bind_trace_geometry _ _ _ (measureFixed_trace_geometry shape arena arenaBound bound)
      intro measured used usedBound
      cases measured with
      | none => exact unchanged_trace_geometry _ _ usedBound
      | some width =>
        apply bind_trace_geometry _ _ _
          (add_trace_geometry total width {arena with used := used} arenaBound usedBound)
        intro next final finalBound
        exact measureFields_trace_geometry rest next {arena with used := final} arenaBound finalBound
end

theorem fixedSize_trace_geometry (desc : SszNative.Codec.Desc) (arena : Delimited.ArenaState)
    (arenaBound : arena.base + arena.capacity ≤ 2 ^ 64)
    (bound : arena.used ≤ arena.capacity) :
    TraceGeometry arena (FixedSize.fixedSize desc arena) := by
  unfold FixedSize.fixedSize
  split
  · exact measureFixed_trace_geometry desc arena arenaBound bound
  · exact unchanged_trace_geometry _ _ bound

/-- Earlier initialized allocations cannot overlap any later scratch suffix. -/
theorem TraceGeometry.writes_before_future {α : Type} {arena : Delimited.ArenaState}
    {outcome : Serialize.Outcome α} (geometry : TraceGeometry arena outcome)
    (a : BitVec 64) (written : Measure.AllocationWrites outcome.calls a)
    (cursor : Nat) (later : outcome.used ≤ cursor) : a.toNat < arena.base + cursor := by
  have bound := (geometry.writes a written).2
  omega

end SszX86.CodecMeasureFixed

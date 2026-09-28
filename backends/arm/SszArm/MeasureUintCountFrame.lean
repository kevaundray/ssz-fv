import SszArm.MeasureUintCountExec

namespace SszArm.Measure.Uint

open UintCodec

def countPureOps : List CountOp :=
  [.p416, .p420, .p424, .p428, .p432, .p436, .p440, .p2192, .p2196, .p2200,
   .p2216, .p2220, .p2224, .p2228, .p2232, .p2236, .p2240, .p2244, .p2248,
   .p2256, .p2260, .p2264, .p2268, .p2272, .p2276, .p2280, .p2292, .p2296,
   .p2300, .p2308, .p2312]

theorem count_pure_frame (base : BitVec 64) (ops : List CountOp) (s : ArmState)
    (members : ∀ op ∈ ops, op ∈ countPureOps) : NatNarrow.Frame s (countBlock base ops s) := by
  induction ops generalizing s with
  | nil => exact NatNarrow.Frame.refl s
  | cons op ops ih =>
    have member := members op List.mem_cons_self
    have frame : NatNarrow.Frame s (op.effect base s) := by
      cases op <;> simp_all only [countPureOps, List.mem_cons, List.not_mem_nil, or_false,
        reduceCtorEq, false_or, or_self]
      all_goals
        constructor
        · exact CountOp.program _ _ _
        · exact CountOp.error _ _ _
        · intro reg outside
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
          simp (disch := simp_all) [CountOp.effect, put, next, compare32,
            Emit.Dispatch.next, Emit.Dispatch.compare32, state_simp_rules]
        · intro reg; exact CountOp.vector _ _ _ _
        · intro address outside
          simp [CountOp.effect, put, next, compare32,
            Emit.Dispatch.next, Emit.Dispatch.compare32, state_simp_rules]
    exact frame.trans (ih _ (fun op member => members op (List.mem_cons_of_mem _ member)))

end SszArm.Measure.Uint

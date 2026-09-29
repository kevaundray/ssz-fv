import SszArm.NatMulDispatchLeftStages

namespace SszArm.NatMul

open SszNative.Limbs

/-- The left phase's actual join: an immediate right skips the right scan;
a borrowed right is scanned even when the left is zero. -/
def LeftDispatch (s t : ArmState) (base : BitVec 64) (words : List (BitVec 64)) : Prop :=
  if r (.GPR 3#5) s = 0#64 then
    read_pc t = base + (if sigWords words = 0 ∨ r (.GPR 4#5) s = 0#64 then 264#64 else 228#64)
  else
    r (.GPR 21#5) t = BitVec.ofNat 64 (sigWords words) ∧
    r (.GPR 8#5) t = r (.GPR 2#5) s ∧ read_pc t = base + 160#64

theorem small_left_dispatch (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 28#64) (small : r (.GPR 1#5) s = 0#64) :
    ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧ LeftDispatch s t base [r (.GPR 2#5) s] := by
  let headOps := smallLeftHeadOps (r (.GPR 2#5) s)
  let u := block base headOps s
  obtain ⟨runHead, headFrame, headPC⟩ := small_left_head s base hc he ha hp small
  change run headOps.length s = u at runHead
  change ScanFrame s u at headFrame
  change read_pc u = smallLeftHeadPC s base at headPC
  by_cases rightSmall : r (.GPR 3#5) s = 0#64
  · by_cases zero : r (.GPR 2#5) s = 0#64
    · have pc : read_pc u = base + 264#64 := by
        simpa only [smallLeftHeadPC, zero, rightSmall, ↓reduceIte] using headPC
      refine ⟨headOps.length, u, runHead, headFrame, ?_⟩
      simp [LeftDispatch, rightSmall, sigWords, significantCount, zero, pc]
    · have pc : read_pc u = base + 140#64 := by
        simpa only [smallLeftHeadPC, zero, rightSmall, ↓reduceIte] using headPC
      obtain ⟨fuel, t, execution, frame, exitPC⟩ := small_right_finish u base
        (headFrame.code hc) (headFrame.error.trans he) (headFrame.aligned ha) pc
      have finalPC : read_pc t = base +
          (if r (.GPR 4#5) s = 0#64 then 264#64 else 228#64) :=
        exitPC.trans (congrArg (fun word : BitVec 64 =>
          base + (if word = 0#64 then 264#64 else 228#64)) (headFrame.registers 4#5 (by decide)))
      refine ⟨headOps.length + fuel, t, ?_, headFrame.trans frame, ?_⟩
      · rw [run_plus, runHead, execution]
      · simpa [LeftDispatch, rightSmall, sigWords, significantCount, zero] using finalPC
  · let zero := decide (r (.GPR 2#5) s = 0#64)
    let ops := smallLeftFinishOps zero
    let t := block base ops u
    have pc : read_pc u = base + (if zero then 152#64 else 112#64) := by
      simpa only [smallLeftHeadPC, rightSmall, zero, decide_eq_true_eq, ↓reduceIte] using headPC
    have execution : run ops.length u = t := block_run base ops u
      (headFrame.code hc) (headFrame.error.trans he) (headFrame.aligned ha)
      (small_left_finish_follows u base zero pc)
    have frame : ScanFrame u t := scan_pure_frame base ops u (by
      dsimp only [ops, smallLeftFinishOps]; split <;> decide)
    obtain ⟨count, raw, exitPC⟩ :
        r (.GPR 21#5) t = (if zero then 0#64 else 1#64) ∧
        r (.GPR 8#5) t = (if zero then 0#64 else r (.GPR 2#5) u) ∧
        read_pc t = base + 160#64 := small_left_finish_values u base zero pc
    refine ⟨headOps.length + ops.length, t, ?_, headFrame.trans frame, ?_⟩
    · rw [run_plus, runHead, execution]
    · simp only [LeftDispatch, rightSmall, ↓reduceIte]
      refine ⟨?_, ?_, exitPC⟩
      · by_cases empty : r (.GPR 2#5) s = 0#64 <;>
          simpa [zero, sigWords, significantCount, empty] using count
      · apply raw.trans
        by_cases empty : r (.GPR 2#5) s = 0#64 <;>
          simp [zero, empty, headFrame.registers 2#5 (by decide)]

/-- The large-left/small-right join first tests the actual significant index;
only a nonzero index reaches the immediate right-word test at +140. -/
theorem small_right_route (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 136#64) :
    ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧ read_pc t = base +
      (if r (.GPR 9#5) s = 0#64 ∨ r (.GPR 4#5) s = 0#64 then 264#64 else 228#64) := by
  let u := block base [.p136] s
  have execution : run 1 s = u := block_run base [.p136] s hc he ha ⟨hp, trivial⟩
  have frame : ScanFrame s u := scan_pure_frame base [.p136] s (by decide)
  have pc : read_pc u = base + (if r (.GPR 9#5) s = 0#64 then 264#64 else 140#64) :=
    small_right_guard_values s base
  by_cases zero : r (.GPR 9#5) s = 0#64
  · exact ⟨1, u, execution, frame, by simpa only [zero, true_or, ↓reduceIte] using pc⟩
  · obtain ⟨fuel, t, rest, finalFrame, exitPC⟩ := small_right_finish u base
      (frame.code hc) (frame.error.trans he) (frame.aligned ha) (by simpa only [zero, ↓reduceIte] using pc)
    have finalPC := exitPC.trans (congrArg (fun word : BitVec 64 =>
      base + (if word = 0#64 then 264#64 else 228#64)) (frame.registers 4#5 (by decide)))
    refine ⟨1 + fuel, t, ?_, frame.trans finalFrame, ?_⟩
    · rw [run_plus, execution, rest]
    · simpa only [zero, false_or, ↓reduceIte] using finalPC

end SszArm.NatMul

import SszArm.MeasureUintCountFinish

namespace SszArm.Measure.Uint

def largeCountOps : List CountOp := [.p416, .p420, .p424, .p428, .p432, .p436, .p440]

/-- Executes the widened significant-limb-count arithmetic before the lowered
CLZ. The final quotient is mathematical, with no machine-word cap assumption. -/
theorem large_count (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 416#64) (safe : 16 ≤ (r (.GPR 31#5) s).toNat)
    (positive : 0 < (r (.GPR 10#5) s).toNat) :
    ∃ fuel t, run fuel s = t ∧ NatNarrow.Frame s t ∧
      read_pc t = base + 2736#64 ∧
      pairValue (r (.GPR 8#5) t) (r (.GPR 9#5) t) =
        (64 * ((r (.GPR 10#5) s).toNat - 1) +
          SszNative.Serialize.bitLength (r (.GPR 11#5) s).toNat + 7) / 8 := by
  let u := countBlock base largeCountOps s
  have pc' : r .PC s = base + 416#64 := pc
  have follows : CountFollows base largeCountOps s := by
    simp [largeCountOps, CountFollows, CountOp.row, CountOp.effect, put, next,
      Emit.Dispatch.next, state_simp_rules, pc', BitVec.add_assoc]
  have executed : run 7 s = u := count_run base largeCountOps s code error aligned follows
  have frame : NatNarrow.Frame s u := count_pure_frame base _ s (by decide)
  have nextPC : read_pc u = base + 2204#64 := by
    simp [u, countBlock, largeCountOps, CountOp.effect, put, next,
      Emit.Dispatch.next, state_simp_rules]
  have limbWord : r (.GPR 8#5) u = r (.GPR 11#5) s := by
    simp [u, countBlock, largeCountOps, CountOp.effect, put, next,
      Emit.Dispatch.next, state_simp_rules]
  have bitPrefix : pairValue (r (.GPR 10#5) u) (r (.GPR 9#5) u) =
      64 * (r (.GPR 10#5) s).toNat - 57 := by
    simpa [u, countBlock, largeCountOps, CountOp.effect, put, next,
      Emit.Dispatch.next, state_simp_rules] using count_sub57 (r (.GPR 10#5) s) positive
  have bitBound := (bitLength_shift_facts (r (.GPR 8#5) u)).1
  have countBound := (r (.GPR 10#5) s).isLt
  obtain ⟨extra, t, finishRun, finishFrame, finishPC, required⟩ :=
    count_finish u base (64 * (r (.GPR 10#5) s).toNat - 57)
      (code.congr frame.program) (frame.error.trans error) (frame.aligned aligned)
      nextPC (by simpa only [frame.sp] using safe) bitPrefix (by omega)
  refine ⟨7 + extra, t, ?_, frame.trans finishFrame, finishPC, ?_⟩
  · rw [run_plus, executed, finishRun]
  · rw [required, limbWord]
    congr 1
    omega

end SszArm.Measure.Uint

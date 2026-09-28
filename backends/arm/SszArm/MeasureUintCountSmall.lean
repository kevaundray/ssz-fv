import SszArm.MeasureUintCountFinish

namespace SszArm.Measure.Uint

def smallCountOps (limbWord : BitVec 64) : List CountOp :=
  [.p2192, .p2196] ++ if limbWord = 0#64 then [] else [.p2200]

theorem small_count (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 2192#64) (safe : 16 ≤ (r (.GPR 31#5) s).toNat) :
    ∃ fuel t, run fuel s = t ∧ NatNarrow.Frame s t ∧
      read_pc t = base + 2736#64 ∧
      pairValue (r (.GPR 8#5) t) (r (.GPR 9#5) t) =
        SszNative.Serialize.requiredBytes (r (.GPR 8#5) s).toNat := by
  let ops := smallCountOps (r (.GPR 8#5) s)
  let u := countBlock base ops s
  have pc' : r .PC s = base + 2192#64 := pc
  have follows : CountFollows base ops s := by
    by_cases zero : r (.GPR 8#5) s = 0#64 <;>
      simp [ops, smallCountOps, CountFollows, CountOp.row, CountOp.effect, put, next,
        Emit.Dispatch.next, state_simp_rules, pc', zero, BitVec.add_assoc]
  have executed : run ops.length s = u := count_run base ops s code error aligned follows
  have frame : NatNarrow.Frame s u := count_pure_frame base ops s (by
    dsimp only [ops, smallCountOps]; split <;> decide)
  by_cases zero : r (.GPR 8#5) s = 0#64
  · refine ⟨ops.length, u, executed, frame, ?_, ?_⟩
    · simp [u, ops, smallCountOps, countBlock, CountOp.effect, put, next,
        Emit.Dispatch.next, state_simp_rules, zero]
    · simp [u, ops, smallCountOps, countBlock, CountOp.effect, put, next,
        Emit.Dispatch.next, state_simp_rules, zero, pairValue,
        SszNative.Serialize.requiredBytes, SszNative.Serialize.bitLength]
  · have nextPC : read_pc u = base + 2204#64 := by
      simp [u, ops, smallCountOps, countBlock, CountOp.effect, put, next,
        Emit.Dispatch.next, state_simp_rules, zero, BitVec.add_assoc]
    have limbWord : r (.GPR 8#5) u = r (.GPR 8#5) s := by
      simp [u, ops, smallCountOps, countBlock, CountOp.effect, put, next,
        Emit.Dispatch.next, state_simp_rules, zero]
    have bitPrefix : pairValue (r (.GPR 10#5) u) (r (.GPR 9#5) u) = 7 := by
      simp [u, ops, smallCountOps, countBlock, CountOp.effect, put, next,
        Emit.Dispatch.next, state_simp_rules, zero, pairValue]
    have bitBound := (bitLength_shift_facts (r (.GPR 8#5) u)).1
    obtain ⟨extra, t, finishRun, finishFrame, finishPC, required⟩ := count_finish u base 7
      (code.congr frame.program) (frame.error.trans error) (frame.aligned aligned)
      nextPC (by simpa only [frame.sp] using safe) bitPrefix (by omega)
    refine ⟨ops.length + extra, t, ?_, frame.trans finishFrame, finishPC, ?_⟩
    · rw [run_plus, executed, finishRun]
    · rw [required, limbWord]
      unfold SszNative.Serialize.requiredBytes
      split <;> omega

end SszArm.Measure.Uint

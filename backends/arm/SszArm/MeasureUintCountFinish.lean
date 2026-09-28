import SszArm.MeasureUintCountAdd
import SszArm.MeasureUintClzBlock

namespace SszArm.Measure.Uint

/-- From the real CLZ-lowering entry through the descriptor-load boundary.
The prefix is an original-register observation, not a successful size premise. -/
theorem count_finish (s : ArmState) (base : BitVec 64) (bitPrefix : Nat)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 2204#64) (safe : 16 ≤ (r (.GPR 31#5) s).toNat)
    (prefixValue : pairValue (r (.GPR 10#5) s) (r (.GPR 9#5) s) = bitPrefix)
    (bound : bitPrefix + SszNative.Serialize.bitLength (r (.GPR 8#5) s).toNat < 2^128) :
    ∃ fuel t, run fuel s = t ∧ NatNarrow.Frame s t ∧
      read_pc t = base + 2736#64 ∧
      pairValue (r (.GPR 8#5) t) (r (.GPR 9#5) t) =
        (bitPrefix + SszNative.Serialize.bitLength (r (.GPR 8#5) s).toNat) / 8 := by
  let bits := SszNative.Serialize.bitLength (r (.GPR 8#5) s).toNat
  have bitBound : bits ≤ 64 := (bitLength_shift_facts _).1
  obtain ⟨u, clzRun, clzFrame, clzPC, counter, high, low⟩ :=
    clz_block s base code error aligned pc safe
  obtain ⟨extra, v, addRun, addFrame, addPC, sum⟩ := count_add u base bits
    (code.congr clzFrame.program) (clzFrame.error.trans error) (clzFrame.aligned aligned)
    clzPC bitBound counter (by simpa only [low, high, prefixValue] using bound)
  have frame : NatNarrow.Frame s v := clzFrame.trans addFrame
  let t := countDivideResult v base
  have divideRun : run 8 v = t := count_divide_run v base (code.congr frame.program)
    (frame.error.trans error) (frame.aligned aligned) addPC (by simpa only [frame.sp] using safe)
  refine ⟨10 + 3 * bits + extra + 8, t, ?_,
    frame.trans (count_divide_frame v base (by simpa only [frame.sp] using safe)), ?_, ?_⟩
  · rw [run_plus, run_plus, clzRun, addRun, divideRun]
  · simp [t, countDivideResult, state_simp_rules]
  · rw [count_divide_value, sum, low, high, prefixValue]

end SszArm.Measure.Uint

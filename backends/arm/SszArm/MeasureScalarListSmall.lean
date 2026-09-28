import SszArm.MeasureScalarListSmallEqual

namespace SszArm.Measure.Scalar.Bytes

open Result
open SszNative (NatOperand)

theorem list_small (s : ArmState) (base word : BitVec 64) (size : Nat)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1960#64) (physical : size < 2^64)
    (stackLow : 16 ≤ (r (.GPR 31#5) s).toNat)
    (ptr : r (.GPR 8#5) s = 0#64) (payload : r (.GPR 9#5) s = word)
    (actual : r (.GPR 20#5) s = BitVec.ofNat 64 size) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧ Ready .list t base (.small word) size := by
  let steps := (smallFlagOps (r (.GPR 20#5) s) (r (.GPR 9#5) s)).length
  let u := smallFlagsResult s base
  let v := smallBranchResult u base
  have hu : run steps s = u := small_flags_run s base code error pc
  have uf : NatNarrow.Frame s u := small_flags_frame s base
  have hv : run 7 u = v := small_branch_run u base (code.congr uf.program)
    (uf.error.trans error) (uf.aligned aligned)
    (by simp [u, smallFlagsResult, state_simp_rules]) (by simpa only [uf.sp] using stackLow)
  have vf : NatNarrow.Frame s v := uf.trans
    (small_branch_frame u base (by simpa only [uf.sp] using stackLow))
  have keep (reg : BitVec 5) (ten : reg ≠ 10#5) (eleven : reg ≠ 11#5) :
      r (.GPR reg) v = r (.GPR reg) s := by
    simp [v, smallBranchResult, u, smallFlagsResult, NatCompare.saved,
      NatExact.r_gpr_w, ten, eleven, state_simp_rules]
  have vptr : r (.GPR 8#5) v = 0#64 := (keep _ (by decide) (by decide)).trans ptr
  have vpayload : r (.GPR 9#5) v = word := (keep _ (by decide) (by decide)).trans payload
  have va : r (.GPR 20#5) v = BitVec.ofNat 64 size := (keep _ (by decide) (by decide)).trans actual
  by_cases same : (r (.GPR 20#5) s = 0#64 ↔ r (.GPR 9#5) s = 0#64)
  · have vp : read_pc v = base + 2048#64 := by
      simp [v, smallBranchResult, u, smallFlagsResult, same, state_simp_rules]
    obtain ⟨fuel, t, ht, tf, ready⟩ := small_equal v base word size
      (code.congr vf.program) (vf.error.trans error) vp physical vptr vpayload va
    exact ⟨steps + 7 + fuel, t, by rw [run_plus, run_plus, hu, hv, ht],
      (Frame.of_narrow vf).trans tf, ready⟩
  · have vp : read_pc v = base + 2388#64 := by
      simp [v, smallBranchResult, u, smallFlagsResult, same, state_simp_rules]
    have selection : (r (.GPR 10#5) v).setWidth 32 = 0#32 ↔ size ≤ (NatOperand.small word).value := by
      have sizeZero : BitVec.ofNat 64 size = 0#64 ↔ size = 0 := by bv_omega
      have wordZero : word = 0#64 ↔ word.toNat = 0 := by bv_omega
      by_cases empty : size = 0 <;> by_cases capZero : word = 0#64 <;>
        simp_all [v, smallBranchResult, u, smallFlagsResult, NatCompare.saved,
          state_simp_rules, actual, payload, NatOperand.value, NatOperand.words, SszNative.Limbs.value]
      all_goals bv_omega
    obtain ⟨fuel, t, ht, tf, ready⟩ := list_marker v base (.small word) size
      (code.congr vf.program) (vf.error.trans error) vp vptr vpayload va selection
    exact ⟨steps + 7 + fuel, t, by rw [run_plus, run_plus, hu, hv, ht],
      (Frame.of_narrow vf).trans tf, ready⟩

end SszArm.Measure.Scalar.Bytes

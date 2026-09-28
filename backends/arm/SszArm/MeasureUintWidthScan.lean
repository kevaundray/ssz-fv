import SszArm.MeasureUintWidthFrame
import SszArm.NatCompareOrder

namespace SszArm.Measure.Uint

open SszNative.Limbs

def widthGuardOps : List WidthOp := [.p2748, .p2752]
def widthTailOps : List WidthOp := [.p2788, .p2792, .p2796]

def widthRoundResult (s : ArmState) (base limb : BitVec 64) : ArmState :=
  widthBlock base widthTailOps (widthLoadResult (widthBlock base widthGuardOps s) base limb)

theorem width_scan_round (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (n : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 2748#64)
    (hptr : r (.GPR 21#5) s = pointer)
    (hn : n < words.length) (hindex : r (.GPR 11#5) s = BitVec.ofNat 64 n)
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    let t := widthRoundResult s base (words[n]?.getD 0#64)
    run 13 s = t ∧ NatNarrow.Frame s t ∧
      r (.GPR 21#5) t = pointer ∧
      r (.GPR 11#5) t = BitVec.ofNat 64 n - 1#64 ∧
      r (.GPR 10#5) t = BitVec.ofNat 64 n ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧
      r (.GPR 9#5) t = r (.GPR 9#5) s ∧
      read_pc t = base + BitVec.ofNat 64
        (if words[n]?.getD 0#64 = 0#64 then 2748 else 2800) := by
  have hbound : words.length < 2^64 := by have := hs.2.1; omega
  have hnonzero : BitVec.ofNat 64 n + 1#64 ≠ 0#64 := by bv_omega
  let u := widthBlock base widthGuardOps s
  have hpc : r .PC s = base + 2748#64 := hp
  have hfollow : WidthFollows base widthGuardOps s := by
    simp [widthGuardOps, WidthFollows, WidthOp.row, WidthOp.effect, put, next, Emit.Dispatch.next,
      state_simp_rules, hpc, BitVec.add_assoc]
  have hu : run 2 s = u := width_run base widthGuardOps s hc he ha hfollow
  have huf : NatNarrow.Frame s u := width_pure_frame base _ s (by decide)
  have hup : read_pc u = base + 2756#64 := by
    simp [u, widthGuardOps, widthBlock, WidthOp.effect, put, next, Emit.Dispatch.next,
      state_simp_rules, hindex, hnonzero]
  have hui : r (.GPR 11#5) u = BitVec.ofNat 64 n := by
    simpa [u, widthGuardOps, widthBlock, WidthOp.effect, put, next, Emit.Dispatch.next,
      state_simp_rules] using hindex
  have huptr : r (.GPR 21#5) u = pointer := by
    simpa [u, widthGuardOps, widthBlock, WidthOp.effect, put, next, Emit.Dispatch.next,
      state_simp_rules] using hptr
  have hus := huf.source pointer words hs
  have hum := huf.words pointer words hs hm
  have hread : read_mem_bytes 8 (r (.GPR 21#5) u + (r (.GPR 11#5) u <<< 3))
      (NatCompare.saved u 9#5) = words[n]?.getD 0#64 := by
    rw [hui, huptr]
    exact NatCompare.limb_load u pointer words n 9#5 hn hus hum
  let v := widthLoadResult u base (words[n]?.getD 0#64)
  have hv : run 8 u = v := width_load_run u base _ (hc.congr huf.program)
    (huf.error.trans he) (huf.aligned ha) hup hus.1 hread
  have hvf : NatNarrow.Frame s v := huf.trans (width_load_frame u base _ hus.1)
  have htail : WidthFollows base widthTailOps v := by
    simp [v, widthTailOps, widthLoadResult, WidthFollows, WidthOp.row, WidthOp.effect,
      put, next, Emit.Dispatch.next, state_simp_rules, BitVec.add_assoc]
  have ht : run 3 v = widthBlock base widthTailOps v := width_run base widthTailOps v
    (hc.congr hvf.program) (hvf.error.trans he) (hvf.aligned ha) htail
  refine ⟨?_, hvf.trans (width_pure_frame base _ v (by decide)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 13 = 2 + 8 + 3 by decide, run_plus, run_plus, hu, hv, ht]
    rfl
  all_goals simp [widthRoundResult, widthTailOps, widthLoadResult, widthGuardOps,
    widthBlock, WidthOp.effect, put, next, Emit.Dispatch.next, NatCompare.saved,
    state_simp_rules, hindex, hptr, apply_ite]

/-- A physically padded descriptor scans its entire high-zero suffix. The
exit count is significantCount, never the number of allocated limbs. -/
theorem width_scan (base pointer : BitVec 64) (words : List (BitVec 64)) :
    ∀ n (s : ArmState), n ≤ words.length →
      CodeAt s base → read_err s = .None → CheckSPAlignment s →
      read_pc s = base + 2748#64 →
      r (.GPR 21#5) s = pointer →
      r (.GPR 11#5) s = BitVec.ofNat 64 n - 1#64 →
      NatCompare.Source s pointer words → NatCompare.Words s pointer words →
      ∃ fuel t, run fuel s = t ∧ NatNarrow.Frame s t ∧
        r (.GPR 21#5) t = pointer ∧
        read_pc t = base + BitVec.ofNat 64
          (if significantCount words n = 0 then 2876 else 2800) ∧
        (significantCount words n ≠ 0 →
          r (.GPR 10#5) t = BitVec.ofNat 64 (significantCount words n - 1)) ∧
        r (.GPR 8#5) t = r (.GPR 8#5) s ∧
        r (.GPR 9#5) t = r (.GPR 9#5) s := by
  intro n
  induction n with
  | zero =>
    intro s hn hc he ha hp hptr hindex hs hm
    let t := widthBlock base widthGuardOps s
    have hpc : r .PC s = base + 2748#64 := hp
    have hf : WidthFollows base widthGuardOps s := by
      simp [widthGuardOps, WidthFollows, WidthOp.row, WidthOp.effect, put, next, Emit.Dispatch.next,
        state_simp_rules, hpc, BitVec.add_assoc]
    refine ⟨2, t, width_run base widthGuardOps s hc he ha hf,
      width_pure_frame base _ s (by decide), ?_, ?_, ?_, ?_, ?_⟩
    · simpa [t, widthGuardOps, widthBlock, WidthOp.effect, put, next, Emit.Dispatch.next,
        state_simp_rules] using hptr
    · simp [t, widthGuardOps, significantCount, widthBlock, WidthOp.effect, put, next,
        Emit.Dispatch.next, state_simp_rules, hindex]
    · simp [significantCount]
    · simp [t, widthGuardOps, widthBlock, WidthOp.effect, put, next,
        Emit.Dispatch.next, state_simp_rules]
    · simp [t, widthGuardOps, widthBlock, WidthOp.effect, put, next,
        Emit.Dispatch.next, state_simp_rules]
  | succ n ih =>
    intro s hn hc he ha hp hptr hindex hs hm
    have hindex' : r (.GPR 11#5) s = BitVec.ofNat 64 n := by
      simpa [BitVec.ofNat_add, BitVec.add_sub_cancel] using hindex
    obtain ⟨hu, huf, huptr, hui, hur, hu8, hu9, hup⟩ :=
      width_scan_round s base pointer words n hc he ha hp hptr (by omega) hindex' hs hm
    let u := widthRoundResult s base (words[n]?.getD 0#64)
    change run 13 s = u at hu
    change NatNarrow.Frame s u at huf
    change r (.GPR 21#5) u = pointer at huptr
    change r (.GPR 11#5) u = BitVec.ofNat 64 n - 1#64 at hui
    change r (.GPR 10#5) u = BitVec.ofNat 64 n at hur
    change read_pc u = base + BitVec.ofNat 64
      (if words[n]?.getD 0#64 = 0#64 then 2748 else 2800) at hup
    by_cases hz : words[n]?.getD 0#64 = 0#64
    · obtain ⟨fuel, t, ht, htf, htpointer, htp, htr, ht8, ht9⟩ := ih u (by omega)
        (hc.congr huf.program) (huf.error.trans he) (huf.aligned ha)
        (by simpa [hz] using hup) huptr hui (huf.source _ _ hs) (huf.words _ _ hs hm)
      refine ⟨13 + fuel, t, ?_, huf.trans htf, htpointer, ?_, ?_, ht8.trans hu8, ht9.trans hu9⟩
      · rw [run_plus, hu, ht]
      · simpa [significantCount, hz] using htp
      · simpa [significantCount, hz] using htr
    · refine ⟨13, u, hu, huf, huptr, ?_, ?_, hu8, hu9⟩
      · simpa [significantCount, hz] using hup
      · intro positive
        simpa [significantCount, hz] using hur

end SszArm.Measure.Uint

import SszArm.EmitUintScanFrame
import SszArm.NatCompareOrder

namespace SszArm.Emit.Uint

open SszNative.Limbs

def scanGuardOps : List WidthOp := [.p80, .p84]
def scanTailOps : List WidthOp := [.p120, .p124, .p128]

def scanRoundResult (s : ArmState) (base limb : BitVec 64) : ArmState :=
  widthBlock base scanTailOps (scanLoadResult (widthBlock base scanGuardOps s) base limb)

theorem significant_scan_round (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (n : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 80#64)
    (hptr : r (.GPR 8#5) s = pointer)
    (hn : n < words.length) (hindex : r (.GPR 10#5) s = BitVec.ofNat 64 n)
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    let t := scanRoundResult s base (words[n]?.getD 0#64)
    run 13 s = t ∧ NatNarrow.Frame s t ∧
      r (.GPR 8#5) t = pointer ∧
      r (.GPR 10#5) t = BitVec.ofNat 64 n - 1#64 ∧
      r (.GPR 9#5) t = BitVec.ofNat 64 n ∧
      read_pc t = base + BitVec.ofNat 64
        (if words[n]?.getD 0#64 = 0#64 then 80 else 132) := by
  have hbound : words.length < 2^64 := by have := hs.2.1; omega
  have hnonzero : BitVec.ofNat 64 n + 1#64 ≠ 0#64 := by bv_omega
  let u := widthBlock base scanGuardOps s
  have hpc : r .PC s = base + 80#64 := hp
  have hfollow : WidthFollows base scanGuardOps s := by
    simp [scanGuardOps, WidthFollows, WidthOp.row, WidthOp.effect, put, next, Dispatch.next,
      state_simp_rules, hpc, BitVec.add_assoc]
  have hu : run 2 s = u := width_run base scanGuardOps s hc he ha hfollow
  have huf : NatNarrow.Frame s u := scan_pure_frame base _ s (by decide)
  have hup : read_pc u = base + 88#64 := by
    simp [u, scanGuardOps, widthBlock, WidthOp.effect, put, next, Dispatch.next,
      state_simp_rules, hindex, hnonzero]
  have hui : r (.GPR 10#5) u = BitVec.ofNat 64 n := by
    simpa [u, scanGuardOps, widthBlock, WidthOp.effect, put, next, Dispatch.next,
      state_simp_rules] using hindex
  have huptr : r (.GPR 8#5) u = pointer := by
    simpa [u, scanGuardOps, widthBlock, WidthOp.effect, put, next, Dispatch.next,
      state_simp_rules] using hptr
  have hus := huf.source pointer words hs
  have hum := huf.words pointer words hs hm
  have hread : read_mem_bytes 8 (r (.GPR 8#5) u + (r (.GPR 10#5) u <<< 3))
      (NatCompare.saved u 9#5) = words[n]?.getD 0#64 := by
    rw [hui, huptr]
    exact NatCompare.limb_load u pointer words n 9#5 hn hus hum
  let v := scanLoadResult u base (words[n]?.getD 0#64)
  have hv : run 8 u = v := scan_load_run u base _ (scan_frame_code huf hc)
    (huf.error.trans he) (huf.aligned ha) hup hus.1 hread
  have hvf : NatNarrow.Frame s v := huf.trans (scan_load_frame u base _ hus.1)
  have htail : WidthFollows base scanTailOps v := by
    simp [v, scanTailOps, scanLoadResult, WidthFollows, WidthOp.row, WidthOp.effect,
      put, next, Dispatch.next, state_simp_rules, BitVec.add_assoc]
  have ht : run 3 v = widthBlock base scanTailOps v := width_run base scanTailOps v
    (scan_frame_code hvf hc) (hvf.error.trans he) (hvf.aligned ha) htail
  refine ⟨?_, hvf.trans (scan_pure_frame base _ v (by decide)), ?_, ?_, ?_, ?_⟩
  · rw [show 13 = 2 + 8 + 3 by decide, run_plus, run_plus, hu, hv, ht]
    rfl
  all_goals simp [scanRoundResult, scanTailOps, scanLoadResult, scanGuardOps,
    widthBlock, WidthOp.effect, put, next, Dispatch.next, NatCompare.saved,
    state_simp_rules, hindex, hptr, apply_ite]

/-- A physically padded descriptor scans its entire high-zero suffix. The
exit count is significantCount, never the number of allocated limbs. -/
theorem significant_scan (base pointer : BitVec 64) (words : List (BitVec 64)) :
    ∀ n (s : ArmState), n ≤ words.length →
      CodeAt s base → read_err s = .None → CheckSPAlignment s →
      read_pc s = base + 80#64 →
      r (.GPR 8#5) s = pointer →
      r (.GPR 10#5) s = BitVec.ofNat 64 n - 1#64 →
      NatCompare.Source s pointer words → NatCompare.Words s pointer words →
      ∃ fuel t, run fuel s = t ∧ NatNarrow.Frame s t ∧
        r (.GPR 8#5) t = pointer ∧
        read_pc t = base + BitVec.ofNat 64
          (if significantCount words n = 0 then 896 else 132) ∧
        (significantCount words n ≠ 0 →
          r (.GPR 9#5) t = BitVec.ofNat 64 (significantCount words n - 1)) := by
  intro n
  induction n with
  | zero =>
    intro s hn hc he ha hp hptr hindex hs hm
    let t := widthBlock base scanGuardOps s
    have hpc : r .PC s = base + 80#64 := hp
    have hf : WidthFollows base scanGuardOps s := by
      simp [scanGuardOps, WidthFollows, WidthOp.row, WidthOp.effect, put, next, Dispatch.next,
        state_simp_rules, hpc, BitVec.add_assoc]
    refine ⟨2, t, width_run base scanGuardOps s hc he ha hf,
      scan_pure_frame base _ s (by decide), ?_, ?_, ?_⟩
    · simpa [t, scanGuardOps, widthBlock, WidthOp.effect, put, next, Dispatch.next,
        state_simp_rules] using hptr
    · simp [t, scanGuardOps, significantCount, widthBlock, WidthOp.effect, put, next,
        Dispatch.next, state_simp_rules, hindex]
    · simp [significantCount]
  | succ n ih =>
    intro s hn hc he ha hp hptr hindex hs hm
    have hindex' : r (.GPR 10#5) s = BitVec.ofNat 64 n := by
      simpa [BitVec.ofNat_add, BitVec.add_sub_cancel] using hindex
    obtain ⟨hu, huf, huptr, hui, hur, hup⟩ :=
      significant_scan_round s base pointer words n hc he ha hp hptr (by omega) hindex' hs hm
    let u := scanRoundResult s base (words[n]?.getD 0#64)
    change run 13 s = u at hu
    change NatNarrow.Frame s u at huf
    change r (.GPR 8#5) u = pointer at huptr
    change r (.GPR 10#5) u = BitVec.ofNat 64 n - 1#64 at hui
    change r (.GPR 9#5) u = BitVec.ofNat 64 n at hur
    change read_pc u = base + BitVec.ofNat 64
      (if words[n]?.getD 0#64 = 0#64 then 80 else 132) at hup
    by_cases hz : words[n]?.getD 0#64 = 0#64
    · obtain ⟨fuel, t, ht, htf, htpointer, htp, htr⟩ := ih u (by omega)
        (scan_frame_code huf hc) (huf.error.trans he) (huf.aligned ha)
        (by simpa [hz] using hup) huptr hui (huf.source _ _ hs) (huf.words _ _ hs hm)
      refine ⟨13 + fuel, t, ?_, huf.trans htf, htpointer, ?_, ?_⟩
      · rw [run_plus, hu, ht]
      · simpa [significantCount, hz] using htp
      · simpa [significantCount, hz] using htr
    · refine ⟨13, u, hu, huf, huptr, ?_, ?_⟩
      · simpa [significantCount, hz] using hup
      · intro positive
        simpa [significantCount, hz] using hur

end SszArm.Emit.Uint

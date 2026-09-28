import SszArm.NatToU128Memory
import SszArm.NatCompareOrder

namespace SszArm.NatToU128

open UintCodec SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def scanLoadOps : List Op := [.p16, .p20, .p24, .p28, .p32, .p36, .p40, .p44]

def scanLoadResult (s : ArmState) (base limb : BitVec 64) : ArmState :=
  w .PC (base + 48#64) (w (.GPR 10#5) limb (NatCompare.saved s 11#5))

theorem scan_load_run (s : ArmState) (base limb : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 16#64)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat)
    (hread : read_mem_bytes 8 (r (.GPR 1#5) s + (r (.GPR 9#5) s <<< 3))
      (NatCompare.saved s 11#5) = limb) :
    run 8 s = scanLoadResult s base limb := by
  have hrestore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64)
      (NatCompare.saved s 11#5) = r (.GPR 11#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  have hpc : r .PC s = base + 16#64 := hp
  have hf : Follows base scanLoadOps s := by
    simp [scanLoadOps, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, hpc, BitVec.add_assoc]
  rw [show 8 = scanLoadOps.length by rfl, block_run base scanLoadOps s hc he ha hf]
  simp only [NatCompare.saved] at hread hrestore
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases f with
    | GPR reg =>
      by_cases hd : reg = 10#5 <;> by_cases ht : reg = 11#5 <;>
        by_cases hsp : reg = 31#5 <;> (try subst reg) <;>
        simp_all (config := {decide := true, instances := true})
          [scanLoadResult, scanLoadOps, block, Op.effect, put, next, NatCompare.saved,
            state_simp_rules, NatCompare.read_spill_w, BitVec.sub_add_cancel,
            BitVec.add_assoc]
    | PC =>
      simp_all (config := {decide := true, instances := true})
        [scanLoadResult, scanLoadOps, block, Op.effect, put, next, NatCompare.saved,
          state_simp_rules, NatCompare.read_spill_w, BitVec.sub_add_cancel,
          BitVec.add_assoc]
    | SFP reg => simp [scanLoadResult, scanLoadOps, block, Op.effect,
        put, next, NatCompare.saved, state_simp_rules]
    | FLAG flag => simp [scanLoadResult, scanLoadOps, block, Op.effect,
        put, next, NatCompare.saved, state_simp_rules]
    | ERR => simp [scanLoadResult, scanLoadOps, block, Op.effect,
        put, next, NatCompare.saved, state_simp_rules]
  · simp [scanLoadResult, scanLoadOps, block, Op.effect, put, next,
      NatCompare.saved, state_simp_rules]
  · intro n addr
    simp [scanLoadResult, scanLoadOps, block, Op.effect, put, next,
      NatCompare.saved, state_simp_rules, NatCompare.read_spill_w]

theorem scan_load_frame (s : ArmState) (base limb : BitVec 64)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat) :
    NatNarrow.Frame s (scanLoadResult s base limb) := by
  have hf := NatNarrow.saved_frame s 11#5 hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [scanLoadResult, state_simp_rules] using hf.program
  · simpa [scanLoadResult, state_simp_rules] using hf.error
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp (disch := simp_all) [scanLoadResult, NatCompare.saved, state_simp_rules]
  · intro reg; simpa [scanLoadResult, state_simp_rules] using hf.vectors reg
  · intro a ha; simpa [scanLoadResult, state_simp_rules] using hf.memory a ha

def scanGuardOps : List Op := [.p8, .p12]
def scanTailOps : List Op := [.p48, .p52, .p56]

def scanRoundResult (s : ArmState) (base limb : BitVec 64) : ArmState :=
  block base scanTailOps (scanLoadResult (block base scanGuardOps s) base limb)

theorem significant_scan_round (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (n : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 8#64)
    (hptr : r (.GPR 1#5) s = pointer)
    (hn : n < words.length) (hindex : r (.GPR 9#5) s = BitVec.ofNat 64 n)
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    let t := scanRoundResult s base (words[n]?.getD 0#64)
    run 13 s = t ∧ NatNarrow.Frame s t ∧
      (∀ reg ∈ [1#5, 2#5], r (.GPR reg) t = r (.GPR reg) s) ∧
      r (.GPR 9#5) t = BitVec.ofNat 64 n - 1#64 ∧
      r (.GPR 8#5) t = BitVec.ofNat 64 n ∧
      read_pc t = base + BitVec.ofNat 64
        (if words[n]?.getD 0#64 = 0#64 then 8 else 60) := by
  have hbound : words.length < 2^64 := by have := hs.2.1; omega
  have hnonzero : BitVec.ofNat 64 n + 1#64 ≠ 0#64 := by bv_omega
  let u := block base scanGuardOps s
  have hpc : r .PC s = base + 8#64 := hp
  have hfollow : Follows base scanGuardOps s := by
    simp [scanGuardOps, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, hpc, BitVec.add_assoc]
  have hu : run 2 s = u := block_run base scanGuardOps s hc he ha hfollow
  have huf : NatNarrow.Frame s u := scan_pure_frame base _ s (by decide)
  have hup : read_pc u = base + 16#64 := by
    simp [u, scanGuardOps, block, Op.effect, put, next,
      state_simp_rules, hindex, hnonzero]
  have hui : r (.GPR 9#5) u = BitVec.ofNat 64 n := by
    simpa [u, scanGuardOps, block, Op.effect, put, next, state_simp_rules] using hindex
  have huptr : r (.GPR 1#5) u = pointer := by
    simpa [u, scanGuardOps, block, Op.effect, put, next, state_simp_rules] using hptr
  have hus := huf.source pointer words hs
  have hum := huf.words pointer words hs hm
  have hread : read_mem_bytes 8 (r (.GPR 1#5) u + (r (.GPR 9#5) u <<< 3))
      (NatCompare.saved u 11#5) = words[n]?.getD 0#64 := by
    rw [hui, huptr]
    exact NatCompare.limb_load u pointer words n 11#5 hn hus hum
  let v := scanLoadResult u base (words[n]?.getD 0#64)
  have hv : run 8 u = v := scan_load_run u base _ (frame_code huf hc)
    (huf.error.trans he) (huf.aligned ha) hup hus.1 hread
  have hvf : NatNarrow.Frame s v := huf.trans (scan_load_frame u base _ hus.1)
  have htail : Follows base scanTailOps v := by
    simp [v, scanTailOps, scanLoadResult, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, BitVec.add_assoc]
  have ht : run 3 v = block base scanTailOps v := block_run base scanTailOps v
    (frame_code hvf hc) (hvf.error.trans he) (hvf.aligned ha) htail
  refine ⟨?_, hvf.trans (scan_pure_frame base _ v (by decide)), ?_, ?_, ?_, ?_⟩
  · rw [show 13 = 2 + 8 + 3 by decide, run_plus, run_plus, hu, hv, ht]
    rfl
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      simp [scanRoundResult, scanTailOps, scanLoadResult, scanGuardOps,
        block, Op.effect, put, next, NatCompare.saved, state_simp_rules]
  all_goals simp [scanRoundResult, scanTailOps, scanLoadResult, scanGuardOps,
    block, Op.effect, put, next, NatCompare.saved, state_simp_rules, hindex, apply_ite]

/-- The actual descending loop terminates for any physically stored limb list,
including empty slices and arbitrary redundant high zero suffixes. -/
theorem significant_scan (base pointer : BitVec 64) (words : List (BitVec 64)) :
    ∀ n (s : ArmState), n ≤ words.length →
      CodeAt s base → read_err s = .None → CheckSPAlignment s →
      read_pc s = base + 8#64 →
      r (.GPR 1#5) s = pointer →
      r (.GPR 9#5) s = BitVec.ofNat 64 n - 1#64 →
      NatCompare.Source s pointer words → NatCompare.Words s pointer words →
      ∃ fuel t, run fuel s = t ∧ NatNarrow.Frame s t ∧
        (∀ reg ∈ [1#5, 2#5], r (.GPR reg) t = r (.GPR reg) s) ∧
        read_pc t = base + BitVec.ofNat 64
          (if significantCount words n = 0 then 120 else 60) ∧
        (significantCount words n ≠ 0 →
          r (.GPR 8#5) t = BitVec.ofNat 64 (significantCount words n - 1)) := by
  intro n
  induction n with
  | zero =>
    intro s hn hc he ha hp hptr hindex hs hm
    let t := block base scanGuardOps s
    have hpc : r .PC s = base + 8#64 := hp
    have hf : Follows base scanGuardOps s := by
      simp [scanGuardOps, Follows, Op.row, Op.effect, put, next,
        state_simp_rules, hpc, BitVec.add_assoc]
    refine ⟨2, t, block_run base scanGuardOps s hc he ha hf,
      scan_pure_frame base _ s (by decide), ?_, ?_, ?_⟩
    · intro reg hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        simp [t, scanGuardOps, block, Op.effect, put, next, state_simp_rules]
    · simp [t, scanGuardOps, significantCount, block, Op.effect, put, next,
        state_simp_rules, hindex]
    · simp [significantCount]
  | succ n ih =>
    intro s hn hc he ha hp hptr hindex hs hm
    have hindex' : r (.GPR 9#5) s = BitVec.ofNat 64 n := by
      simpa [BitVec.ofNat_add, BitVec.add_sub_cancel] using hindex
    obtain ⟨hu, huf, hkeep, hui, hur, hup⟩ :=
      significant_scan_round s base pointer words n hc he ha hp hptr (by omega) hindex' hs hm
    let u := scanRoundResult s base (words[n]?.getD 0#64)
    change run 13 s = u at hu
    change NatNarrow.Frame s u at huf
    change (∀ reg ∈ [1#5, 2#5], r (.GPR reg) u = r (.GPR reg) s) at hkeep
    change r (.GPR 9#5) u = BitVec.ofNat 64 n - 1#64 at hui
    change r (.GPR 8#5) u = BitVec.ofNat 64 n at hur
    change read_pc u = base + BitVec.ofNat 64
      (if words[n]?.getD 0#64 = 0#64 then 8 else 60) at hup
    by_cases hz : words[n]?.getD 0#64 = 0#64
    · have hupp : r (.GPR 1#5) u = pointer :=
        (hkeep 1#5 (by decide)).trans hptr
      obtain ⟨fuel, t, ht, htf, htk, htp, htr⟩ := ih u (by omega)
        (frame_code huf hc) (huf.error.trans he) (huf.aligned ha)
        (by simpa [hz] using hup) hupp hui (huf.source _ _ hs) (huf.words _ _ hs hm)
      refine ⟨13 + fuel, t, ?_, huf.trans htf,
        fun reg hr => (htk reg hr).trans (hkeep reg hr), ?_, ?_⟩
      · rw [run_plus, hu, ht]
      · simpa [significantCount, hz] using htp
      · simpa [significantCount, hz] using htr
    · refine ⟨13, u, hu, huf, hkeep, ?_, ?_⟩
      · simpa [significantCount, hz] using hup
      · intro positive
        simpa [significantCount, hz] using hur

end SszArm.NatToU128

import SszArm.NatMulNormalizeFrame

namespace SszArm.NatMul

open UintCodec SszNative.Limbs

def normalizeGuard : List Op := [.p1060, .p1064]
def normalizeTail : List Op := [.p1048, .p1052, .p1056]

def normalizeRound (s : ArmState) (base word : BitVec 64) : ArmState :=
  block base normalizeTail (normalizeLoaded (block base normalizeGuard s) base word)

theorem normalize_scan_round (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (n : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1060#64)
    (h20 : r (.GPR 20#5) s = pointer) (h23 : r (.GPR 23#5) s = BitVec.ofNat 64 n)
    (hn : n < words.length) (hs : NatCompare.Source s pointer words)
    (hm : NatCompare.Words s pointer words) :
    let t := normalizeRound s base (words[n]?.getD 0#64)
    run 13 s = t ∧ NormalizeFrame s t ∧ r (.GPR 20#5) t = pointer ∧
      r (.GPR 23#5) t = BitVec.ofNat 64 n - 1#64 ∧
      r (.GPR 8#5) t = BitVec.ofNat 64 n ∧
      read_pc t = if words[n]?.getD 0#64 = 0#64 then base + 1060#64 else base + 1276#64 := by
  have hbound : words.length < 2^64 := by have := hs.2.1; omega
  have hnonzero : BitVec.ofNat 64 n + 1#64 ≠ 0#64 := by bv_omega
  let u := block base normalizeGuard s
  have hpc : r .PC s = base + 1060#64 := hp
  have hf : Follows base normalizeGuard s := by
    simp [normalizeGuard, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, hpc, BitVec.add_assoc]
  have hu : run 2 s = u := block_run base normalizeGuard s hc he ha hf
  have huf := normalize_pure_frame base normalizeGuard s (by decide)
  have hup : read_pc u = base + 1016#64 := by
    simp [u, normalizeGuard, block, Op.effect, put, next, state_simp_rules, h23, hnonzero]
  have hu20 : r (.GPR 20#5) u = pointer := by
    simp [u, normalizeGuard, block, Op.effect, put, next, state_simp_rules, h20]
  have hu23 : r (.GPR 23#5) u = BitVec.ofNat 64 n := by
    simp [u, normalizeGuard, block, Op.effect, put, next, state_simp_rules, h23]
  have hus := huf.source pointer words hs
  obtain ⟨physical, separate, valueAt⟩ :=
    NatMulWord.scan_limb u pointer words n hn hus (huf.words pointer words hs hm)
  let v := normalizeLoaded u base (words[n]?.getD 0#64)
  have hv : run 8 u = v := normalize_load_run u base _
    (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup hus.1
    (by simpa only [hu20, hu23] using physical)
    (by simpa only [hu20, hu23] using separate)
    (by simpa only [hu20, hu23] using valueAt)
  have hvf := huf.trans (normalize_load_frame u base _ hus.1)
  have htail : Follows base normalizeTail v := by
    simp [v, normalizeTail, normalizeLoaded, Follows, Op.row, Op.effect,
      put, next, state_simp_rules, BitVec.add_assoc]
  have ht : run 3 v = block base normalizeTail v :=
    block_run base normalizeTail v (hvf.code hc) (hvf.error.trans he) (hvf.aligned ha) htail
  refine ⟨?_, hvf.trans (normalize_pure_frame base normalizeTail v (by decide)), ?_, ?_, ?_, ?_⟩
  · rw [show 13 = 2 + 8 + 3 by decide, run_plus, run_plus, hu, hv, ht]
    rfl
  all_goals simp [normalizeRound, normalizeGuard, normalizeTail, normalizeLoaded,
    NatCompare.saved, block, Op.effect, put, next, state_simp_rules, h20, h23]

/-- Induction consumes the remaining physical output length. No bound on the
logical multiplication or on its redundant high-zero suffix is imposed. -/
theorem normalize_scan (base pointer : BitVec 64) (words : List (BitVec 64)) :
    ∀ n (s : ArmState), n ≤ words.length →
      CodeAt s base → read_err s = .None → CheckSPAlignment s →
      read_pc s = base + 1060#64 → r (.GPR 20#5) s = pointer →
      r (.GPR 23#5) s = BitVec.ofNat 64 n - 1#64 →
      NatCompare.Source s pointer words → NatCompare.Words s pointer words →
      ∃ fuel t, run fuel s = t ∧ NormalizeFrame s t ∧ r (.GPR 20#5) t = pointer ∧
        read_pc t = (if significantCount words n = 0 then base + 1068#64 else base + 1276#64) ∧
        (significantCount words n ≠ 0 →
          r (.GPR 8#5) t = BitVec.ofNat 64 (significantCount words n - 1)) := by
  intro n
  induction n with
  | zero =>
    intro s hn hc he ha hp h20 h23 hs hm
    let t := block base normalizeGuard s
    have hpc : r .PC s = base + 1060#64 := hp
    have hf : Follows base normalizeGuard s := by
      simp [normalizeGuard, Follows, Op.row, Op.effect, put, next,
        state_simp_rules, hpc, BitVec.add_assoc]
    refine ⟨2, t, block_run base normalizeGuard s hc he ha hf,
      normalize_pure_frame base normalizeGuard s (by decide), ?_, ?_, ?_⟩
    all_goals simp [t, normalizeGuard, block, Op.effect, put, next,
      state_simp_rules, h20, h23, significantCount]
  | succ n ih =>
    intro s hn hc he ha hp h20 h23 hs hm
    have h23' : r (.GPR 23#5) s = BitVec.ofNat 64 n := by
      simpa [BitVec.ofNat_add, BitVec.add_sub_cancel] using h23
    obtain ⟨hu, huf, hu20, hu23, hu8, hup⟩ :=
      normalize_scan_round s base pointer words n hc he ha hp h20 h23' (by omega) hs hm
    let u := normalizeRound s base (words[n]?.getD 0#64)
    change run 13 s = u at hu
    change NormalizeFrame s u at huf
    change r (.GPR 20#5) u = pointer at hu20
    change r (.GPR 23#5) u = BitVec.ofNat 64 n - 1#64 at hu23
    change r (.GPR 8#5) u = BitVec.ofNat 64 n at hu8
    change read_pc u = if words[n]?.getD 0#64 = 0#64 then base + 1060#64 else base + 1276#64 at hup
    by_cases hz : words[n]?.getD 0#64 = 0#64
    · obtain ⟨fuel, t, ht, htf, ht20, htp, ht8⟩ := ih u (by omega)
        (huf.code hc) (huf.error.trans he) (huf.aligned ha)
        (by simpa [hz] using hup) hu20 hu23 (huf.source _ _ hs) (huf.words _ _ hs hm)
      refine ⟨13 + fuel, t, ?_, huf.trans htf, ht20, ?_, ?_⟩
      · rw [run_plus, hu, ht]
      · simpa [significantCount, hz] using htp
      · simpa [significantCount, hz] using ht8
    · refine ⟨13, u, hu, huf, hu20, ?_, ?_⟩
      · simpa [significantCount, hz] using hup
      · intro h; simpa [significantCount, hz] using hu8

end SszArm.NatMul

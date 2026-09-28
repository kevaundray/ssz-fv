import SszArm.NatMulScanLeft

namespace SszArm.NatMul

open SszNative.Limbs

def rightScanRound (s : ArmState) (base word : BitVec 64) : ArmState :=
  block base [.p204, .p208]
    (scanLoadResult (block base [.p164, .p168, .p172] s) base .right word)

theorem right_scan_round (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (n : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 164#64)
    (h3 : r (.GPR 3#5) s = pointer)
    (h9 : r (.GPR 9#5) s = BitVec.ofNat 64 (n + 1))
    (hn : n < words.length) (hs : NatCompare.Source s pointer words)
    (hm : NatCompare.Words s pointer words) :
    let t := rightScanRound s base (words[n]?.getD 0#64)
    run 12 s = t ∧ ScanFrame s t ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧
      r (.GPR 21#5) t = r (.GPR 21#5) s ∧
      r (.GPR 9#5) t = BitVec.ofNat 64 n ∧
      r (.GPR 22#5) t = BitVec.ofNat 64 (n + 1) ∧
      read_pc t = base + (if words[n]?.getD 0#64 = 0#64 then 164#64 else 212#64) := by
  have bound : words.length < 2^64 := by have := hs.2.1; omega
  have nonzero : BitVec.ofNat 64 (n + 1) ≠ 0#64 := by bv_omega
  let u := block base [.p164, .p168, .p172] s
  have hpc : r .PC s = base + 164#64 := hp
  have hu : run 3 s = u := block_run base _ s hc he ha (by
    simp [Follows, Op.row, Op.effect, put, next, state_simp_rules,
      hpc, h9, nonzero, BitVec.add_assoc])
  have huf : ScanFrame s u := scan_pure_frame base _ s (by decide)
  have hup : read_pc u = base + 176#64 := by
    simp [u, block, Op.effect, put, next, state_simp_rules, h9, nonzero, BitVec.add_assoc]
  have hus := huf.source pointer words hs
  have hum := huf.words pointer words hs hm
  have hload : read_mem_bytes 8 (ScanLoad.right.address u)
      (NatCompare.saved u 11#5) = words[n]?.getD 0#64 := by
    have address : ScanLoad.right.address u = pointer + (BitVec.ofNat 64 n <<< 3) := by
      simp [u, ScanLoad.address, block, Op.effect, put, next, state_simp_rules, h3, h9]
      bv_omega
    rw [address]
    exact NatCompare.limb_load u pointer words n 11#5 hn hus hum
  let v := scanLoadResult u base .right (words[n]?.getD 0#64)
  have hv : run 7 u = v := scan_load_run u base _ .right
    (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup hus.1 hload
  have hvf := huf.trans (scan_load_frame u base _ .right hus.1)
  have ht : run 2 v = block base [.p204, .p208] v :=
    block_run base _ v (hvf.code hc) (hvf.error.trans he) (hvf.aligned ha) (by
      simp [v, scanLoadResult, ScanLoad.start, ScanLoad.size, Follows, Op.row,
        Op.effect, put, next, state_simp_rules, BitVec.add_assoc])
  refine ⟨?_, hvf.trans (scan_pure_frame base _ v (by decide)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 12 = 3 + 7 + 2 by decide, run_plus, run_plus, hu, hv, ht]
    rfl
  all_goals simp [rightScanRound, scanLoadResult, ScanLoad.tmp, ScanLoad.dst,
    block, Op.effect, put, next, NatCompare.saved, state_simp_rules, h9]
  all_goals bv_omega

/-- The right scan is performed even when X21 is zero. Its empty/all-zero
exit precedes the left-zero test at +212, just as in the original image. -/
theorem right_scan (base pointer : BitVec 64) (words : List (BitVec 64)) :
    ∀ n (s : ArmState), n ≤ words.length →
      CodeAt s base → read_err s = .None → CheckSPAlignment s →
      read_pc s = base + 164#64 → r (.GPR 3#5) s = pointer →
      r (.GPR 9#5) s = BitVec.ofNat 64 n →
      NatCompare.Source s pointer words → NatCompare.Words s pointer words →
      ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧
        r (.GPR 8#5) t = r (.GPR 8#5) s ∧
        r (.GPR 21#5) t = r (.GPR 21#5) s ∧
        (significantCount words n ≠ 0 →
          r (.GPR 22#5) t = BitVec.ofNat 64 (significantCount words n)) ∧
        (significantCount words n ≠ 0 →
          r (.GPR 9#5) t = BitVec.ofNat 64 (significantCount words n - 1)) ∧
        read_pc t = base + (if significantCount words n = 0 then 264#64 else 212#64) := by
  intro n
  induction n with
  | zero =>
    intro s hn hc he ha hp h3 h9 hs hm
    let t := block base [.p164] s
    have hpc : r .PC s = base + 164#64 := hp
    refine ⟨1, t, block_run base _ s hc he ha (by
      simp [Follows, Op.row, hpc]), scan_pure_frame base _ s (by decide), ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [t, block, Op.effect, put, next, state_simp_rules, h9, significantCount]
  | succ n ih =>
    intro s hn hc he ha hp h3 h9 hs hm
    obtain ⟨hu, huf, hu8, hu21, hu9, hu22, hup⟩ :=
      right_scan_round s base pointer words n hc he ha hp h3 h9 (by omega) hs hm
    let u := rightScanRound s base (words[n]?.getD 0#64)
    change run 12 s = u at hu
    change ScanFrame s u at huf
    change r (.GPR 8#5) u = r (.GPR 8#5) s at hu8
    change r (.GPR 21#5) u = r (.GPR 21#5) s at hu21
    change r (.GPR 9#5) u = BitVec.ofNat 64 n at hu9
    change r (.GPR 22#5) u = BitVec.ofNat 64 (n + 1) at hu22
    change read_pc u = base + (if words[n]?.getD 0#64 = 0#64 then 164#64 else 212#64) at hup
    by_cases zero : words[n]?.getD 0#64 = 0#64
    · obtain ⟨fuel, t, ht, htf, ht8, ht21, ht22, ht9, htp⟩ := ih u (by omega)
        (huf.code hc) (huf.error.trans he) (huf.aligned ha)
        (by simpa [zero] using hup) ((huf.registers 3#5 (by decide)).trans h3) hu9
        (huf.source _ _ hs) (huf.words _ _ hs hm)
      refine ⟨12 + fuel, t, ?_, huf.trans htf, ht8.trans hu8, ht21.trans hu21, ?_, ?_, ?_⟩
      · rw [run_plus, hu, ht]
      · simpa [significantCount, zero] using ht22
      · simpa [significantCount, zero] using ht9
      · simpa [significantCount, zero] using htp
    · refine ⟨12, u, hu, huf, hu8, hu21, ?_, ?_, ?_⟩
      · intro h; simpa [significantCount, zero] using hu22
      · intro h; simpa [significantCount, zero] using hu9
      · simpa [significantCount, zero] using hup

theorem right_large_scan (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 160#64)
    (h3 : r (.GPR 3#5) s = pointer)
    (h4 : r (.GPR 4#5) s = BitVec.ofNat 64 words.length)
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧
      r (.GPR 21#5) t = r (.GPR 21#5) s ∧
      (sigWords words ≠ 0 → r (.GPR 22#5) t = BitVec.ofNat 64 (sigWords words)) ∧
      (sigWords words ≠ 0 → r (.GPR 9#5) t = BitVec.ofNat 64 (sigWords words - 1)) ∧
      read_pc t = base + (if sigWords words = 0 then 264#64 else 212#64) := by
  let u := block base [.p160] s
  have hpc : r .PC s = base + 160#64 := hp
  have hu : run 1 s = u := block_run base _ s hc he ha (by simp [Follows, Op.row, hpc])
  have huf : ScanFrame s u := scan_pure_frame base _ s (by decide)
  have hup : read_pc u = base + 164#64 := by
    simp [u, block, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]
  have hu9 : r (.GPR 9#5) u = BitVec.ofNat 64 words.length := by
    simp [u, block, Op.effect, put, next, state_simp_rules, h4]
  obtain ⟨fuel, t, ht, htf, ht8, ht21, ht22, ht9, htp⟩ := right_scan base pointer words words.length u
    (Nat.le_refl _) (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup
    ((huf.registers 3#5 (by decide)).trans h3) hu9
    (huf.source _ _ hs) (huf.words _ _ hs hm)
  refine ⟨1 + fuel, t, ?_, huf.trans htf, ?_, ?_, ht22, ht9, htp⟩
  · rw [run_plus, hu, ht]
  · simpa [u, block, Op.effect, put, next, state_simp_rules] using ht8
  · simpa [u, block, Op.effect, put, next, state_simp_rules] using ht21

end SszArm.NatMul

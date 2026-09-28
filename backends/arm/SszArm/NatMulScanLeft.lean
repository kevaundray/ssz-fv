import SszArm.NatMulScanLoad

namespace SszArm.NatMul

open SszNative.Limbs

def leftScanRound (s : ArmState) (base word : BitVec 64) : ArmState :=
  block base [.p80, .p84]
    (scanLoadResult (block base [.p40, .p44] s) base .left word)

theorem left_scan_round (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (n : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 40#64)
    (h8 : r (.GPR 8#5) s = pointer - 8#64)
    (h10 : r (.GPR 10#5) s = BitVec.ofNat 64 (n + 1))
    (hn : n < words.length) (hs : NatCompare.Source s pointer words)
    (hm : NatCompare.Words s pointer words) :
    let t := leftScanRound s base (words[n]?.getD 0#64)
    run 12 s = t ∧ ScanFrame s t ∧
      r (.GPR 8#5) t = pointer - 8#64 ∧
      r (.GPR 9#5) t = BitVec.ofNat 64 (n + 1) ∧
      r (.GPR 10#5) t = BitVec.ofNat 64 n ∧
      read_pc t = base + (if words[n]?.getD 0#64 = 0#64 then 40#64 else 88#64) := by
  have bound : words.length < 2^64 := by have := hs.2.1; omega
  have nonzero : BitVec.ofNat 64 (n + 1) ≠ 0#64 := by bv_omega
  let u := block base [.p40, .p44] s
  have hpc : r .PC s = base + 40#64 := hp
  have hu : run 2 s = u := block_run base _ s hc he ha (by
    simp [Follows, Op.row, Op.effect, put, next, state_simp_rules,
      hpc, BitVec.add_assoc])
  have huf : ScanFrame s u := scan_pure_frame base _ s (by decide)
  have hup : read_pc u = base + 48#64 := by
    simp [u, block, Op.effect, put, next, state_simp_rules, h10, nonzero]
  have hus := huf.source pointer words hs
  have hum := huf.words pointer words hs hm
  have hload : read_mem_bytes 8 (ScanLoad.left.address u)
      (NatCompare.saved u 10#5) = words[n]?.getD 0#64 := by
    have address : ScanLoad.left.address u = pointer + (BitVec.ofNat 64 n <<< 3) := by
      simp [u, ScanLoad.address, block, Op.effect, put, next, state_simp_rules, h8, h10]
      bv_omega
    rw [address]
    exact NatCompare.limb_load u pointer words n 10#5 hn hus hum
  let v := scanLoadResult u base .left (words[n]?.getD 0#64)
  have hv : run 8 u = v := scan_load_run u base _ .left
    (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup hus.1 hload
  have hvf := huf.trans (scan_load_frame u base _ .left hus.1)
  have ht : run 2 v = block base [.p80, .p84] v :=
    block_run base _ v (hvf.code hc) (hvf.error.trans he) (hvf.aligned ha) (by
      simp [v, scanLoadResult, ScanLoad.start, ScanLoad.size, Follows, Op.row,
        Op.effect, put, next, state_simp_rules, BitVec.add_assoc])
  refine ⟨?_, hvf.trans (scan_pure_frame base _ v (by decide)), ?_, ?_, ?_, ?_⟩
  · rw [show 12 = 2 + 8 + 2 by decide, run_plus, run_plus, hu, hv, ht]
    rfl
  all_goals simp [leftScanRound, scanLoadResult, ScanLoad.tmp, ScanLoad.dst,
    block, Op.effect, put, next, NatCompare.saved, state_simp_rules, h8, h10]
  all_goals bv_omega

/-- The native descending scan handles empty spans and arbitrarily many
redundant high limbs. Only the physical Source span bounds machine arithmetic. -/
theorem left_scan (base pointer : BitVec 64) (words : List (BitVec 64)) :
    ∀ n (s : ArmState), n ≤ words.length →
      CodeAt s base → read_err s = .None → CheckSPAlignment s →
      read_pc s = base + 40#64 →
      r (.GPR 8#5) s = pointer - 8#64 →
      r (.GPR 10#5) s = BitVec.ofNat 64 n →
      NatCompare.Source s pointer words → NatCompare.Words s pointer words →
      ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧
        r (.GPR 9#5) t = BitVec.ofNat 64 (significantCount words n) ∧
        (significantCount words n ≠ 0 →
          r (.GPR 10#5) t = BitVec.ofNat 64 (significantCount words n - 1)) ∧
        read_pc t = base + (if significantCount words n = 0 then 124#64 else 88#64) := by
  intro n
  induction n with
  | zero =>
    intro s hn hc he ha hp h8 h10 hs hm
    let t := block base [.p40, .p44] s
    have hpc : r .PC s = base + 40#64 := hp
    refine ⟨2, t, block_run base _ s hc he ha (by
      simp [Follows, Op.row, Op.effect, put, next, state_simp_rules,
        hpc, BitVec.add_assoc]), scan_pure_frame base _ s (by decide), ?_, ?_, ?_⟩
    all_goals simp [t, block, Op.effect, put, next, state_simp_rules, h10, significantCount]
  | succ n ih =>
    intro s hn hc he ha hp h8 h10 hs hm
    obtain ⟨hu, huf, hu8, hu9, hu10, hup⟩ :=
      left_scan_round s base pointer words n hc he ha hp h8 h10 (by omega) hs hm
    let u := leftScanRound s base (words[n]?.getD 0#64)
    change run 12 s = u at hu
    change ScanFrame s u at huf
    change r (.GPR 8#5) u = pointer - 8#64 at hu8
    change r (.GPR 9#5) u = BitVec.ofNat 64 (n + 1) at hu9
    change r (.GPR 10#5) u = BitVec.ofNat 64 n at hu10
    change read_pc u = base + (if words[n]?.getD 0#64 = 0#64 then 40#64 else 88#64) at hup
    by_cases zero : words[n]?.getD 0#64 = 0#64
    · obtain ⟨fuel, t, ht, htf, ht9, ht10, htp⟩ := ih u (by omega)
        (huf.code hc) (huf.error.trans he) (huf.aligned ha)
        (by simpa [zero] using hup) hu8 hu10
        (huf.source _ _ hs) (huf.words _ _ hs hm)
      refine ⟨12 + fuel, t, ?_, huf.trans htf, ?_, ?_, ?_⟩
      · rw [run_plus, hu, ht]
      · simpa [significantCount, zero] using ht9
      · simpa [significantCount, zero] using ht10
      · simpa [significantCount, zero] using htp
    · refine ⟨12, u, hu, huf, ?_, ?_, ?_⟩
      · simpa [significantCount, zero] using hu9
      · intro h; simpa [significantCount, zero] using hu10
      · simpa [significantCount, zero] using hup

/-- Original large-left entry and its exact join. X8 is restored to the raw
physical payload, never replaced by the significant count. -/
theorem left_large_scan (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 28#64)
    (h1 : r (.GPR 1#5) s = pointer) (nonzero : pointer ≠ 0#64)
    (h2 : r (.GPR 2#5) s = BitVec.ofNat 64 words.length)
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧
      r (.GPR 21#5) t = BitVec.ofNat 64 (sigWords words) ∧
      r (.GPR 9#5) t = BitVec.ofNat 64 (sigWords words) ∧
      r (.GPR 8#5) t = r (.GPR 2#5) s ∧
      read_pc t = base + (if r (.GPR 3#5) s = 0#64 then 136#64 else 160#64) := by
  let u := block base [.p28, .p32, .p36] s
  have hpc : r .PC s = base + 28#64 := hp
  have hu : run 3 s = u := block_run base _ s hc he ha (by
    simp [Follows, Op.row, Op.effect, put, next, state_simp_rules,
      hpc, h1, nonzero, BitVec.add_assoc])
  have huf : ScanFrame s u := scan_pure_frame base _ s (by decide)
  have hup : read_pc u = base + 40#64 := by
    simp [u, block, Op.effect, put, next, state_simp_rules, h1, nonzero, BitVec.add_assoc]
  have hu8 : r (.GPR 8#5) u = pointer - 8#64 := by
    simp [u, block, Op.effect, put, next, state_simp_rules, h1]
  have hu10 : r (.GPR 10#5) u = BitVec.ofNat 64 words.length := by
    simp [u, block, Op.effect, put, next, state_simp_rules, h2]
  obtain ⟨fuel, v, hv, hvf, hv9, hv10, hvp⟩ := left_scan base pointer words words.length u
    (Nat.le_refl _) (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup hu8 hu10
    (huf.source _ _ hs) (huf.words _ _ hs hm)
  have frame := huf.trans hvf
  have h2v := frame.registers 2#5 (by decide)
  have h3v := frame.registers 3#5 (by decide)
  have bound : sigWords words < 2^64 :=
    Nat.lt_of_le_of_lt (sigWords_le_length words) (by have := hs.2.1; omega)
  let ops : List Op := if sigWords words = 0 then [.p124, .p128, .p132]
    else if r (.GPR 3#5) s = 0#64 then [.p88, .p92, .p96, .p100]
    else [.p88, .p92, .p96]
  let t := block base ops v
  have vpc : r .PC v = base + (if sigWords words = 0 then 124#64 else 88#64) := hvp
  have ht : run ops.length v = t := block_run base ops v
    (frame.code hc) (frame.error.trans he) (frame.aligned ha) (by
      by_cases zero : sigWords words = 0 <;> by_cases rightZero : r (.GPR 3#5) s = 0#64 <;>
        simp [ops, zero, rightZero, Follows, Op.row, Op.effect, put, next,
          state_simp_rules, vpc, h3v, BitVec.add_assoc])
  have htf : ScanFrame v t := scan_pure_frame base ops v (by
    dsimp only [ops]; split <;> (try split) <;> decide)
  refine ⟨3 + fuel + ops.length, t, ?_, frame.trans htf, ?_, ?_, ?_, ?_⟩
  · rw [run_plus, run_plus, hu, hv, ht]
  · by_cases zero : sigWords words = 0
    · simp [t, ops, zero, block, Op.effect, put, next, state_simp_rules]
    · have count := hv10 zero
      have restore : BitVec.ofNat 64 (sigWords words - 1) + 1#64 =
          BitVec.ofNat 64 (sigWords words) := by bv_omega
      by_cases rightZero : r (.GPR 3#5) s = 0#64 <;>
        simp [t, ops, zero, rightZero, block, Op.effect, put, next,
          state_simp_rules, count, restore]
  · by_cases zero : sigWords words = 0 <;> by_cases rightZero : r (.GPR 3#5) s = 0#64 <;>
      simpa [t, ops, zero, rightZero, block, Op.effect, put, next, state_simp_rules] using hv9
  · by_cases zero : sigWords words = 0 <;> by_cases rightZero : r (.GPR 3#5) s = 0#64 <;>
      simp [t, ops, zero, rightZero, block, Op.effect, put, next, state_simp_rules, h2v]
  · by_cases zero : sigWords words = 0 <;> by_cases rightZero : r (.GPR 3#5) s = 0#64 <;>
      simp [t, ops, zero, rightZero, block, Op.effect, put, next, state_simp_rules, h3v]

end SszArm.NatMul

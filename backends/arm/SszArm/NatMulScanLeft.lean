import SszArm.NatMulScanJoin

namespace SszArm.NatMul

open SszNative.Limbs

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
  have hu : run 2 s = u :=
    block_run base [.p40, .p44] s hc he ha (left_head_follows s base hp)
  have huf : ScanFrame s u := scan_pure_frame base [.p40, .p44] s (by decide)
  obtain ⟨head8, head9, headPC⟩ := left_head_values s base
  have hup : read_pc u = base + 48#64 := by
    simpa only [h10, nonzero, ↓reduceIte] using headPC
  have hus := huf.source pointer words hs
  have hum := huf.words pointer words hs hm
  have hload : read_mem_bytes 8 (ScanLoad.left.address u)
      (NatCompare.saved u 10#5) = words[n]?.getD 0#64 := by
    have address : ScanLoad.left.address u = pointer + (BitVec.ofNat 64 n <<< 3) := by
      change r (.GPR 8#5) u + (r (.GPR 9#5) u <<< 3) = _
      rw [head8, head9, h8, h10]
      bv_omega
    rw [address]
    exact NatCompare.limb_load u pointer words n 10#5 hn hus hum
  let v := scanLoadResult u base .left (words[n]?.getD 0#64)
  have hv : run 8 u = v := scan_load_run u base (words[n]?.getD 0#64) .left
    (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup hus.1 hload
  have hvf : ScanFrame s v :=
    huf.trans (scan_load_frame u base (words[n]?.getD 0#64) .left hus.1)
  have ht : run 2 v = block base [.p80, .p84] v :=
    block_run base [.p80, .p84] v (hvf.code hc) (hvf.error.trans he) (hvf.aligned ha)
      (left_tail_follows v base (scan_left_load_values u base (words[n]?.getD 0#64)).2.2.2)
  obtain ⟨out8, out9, out10, outPC⟩ := left_round_values s base (words[n]?.getD 0#64)
  refine ⟨?_, hvf.trans (scan_pure_frame base [.p80, .p84] v (by decide)),
    out8.trans h8, out9.trans h10, ?_, outPC⟩
  · rw [show 12 = 2 + 8 + 2 by decide, run_plus, run_plus, hu, hv, ht]
    rfl
  · rw [out10, h10]
    arm_word_nf
    rw [BitVec.ofNat_add, BitVec.add_sub_cancel]

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
    obtain ⟨head8, head9, headPC⟩ := left_head_values s base
    refine ⟨2, t, block_run base [.p40, .p44] s hc he ha (left_head_follows s base hp),
      scan_pure_frame base [.p40, .p44] s (by decide), ?_, ?_, ?_⟩
    · simpa only [significantCount, h10] using head9
    · simp only [significantCount, ne_eq, not_true_eq_false, false_implies]
    · simpa [significantCount, h10] using headPC
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
  have ptrNonzero : r (.GPR 1#5) s ≠ 0#64 := by simpa only [h1] using nonzero
  have hu : run 3 s = u := block_run base [.p28, .p32, .p36] s hc he ha
    (left_entry_follows s base hp ptrNonzero)
  have huf : ScanFrame s u := scan_pure_frame base [.p28, .p32, .p36] s (by decide)
  obtain ⟨hup, entry8, entry10⟩ := left_entry_values s base ptrNonzero
  have hu8 : r (.GPR 8#5) u = pointer - 8#64 := by
    simpa only [h1] using entry8
  have hu10 : r (.GPR 10#5) u = BitVec.ofNat 64 words.length := entry10.trans h2
  obtain ⟨fuel, v, hv, hvf, hv9, hv10, hvp⟩ := left_scan base pointer words words.length u
    (Nat.le_refl _) (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup hu8 hu10
    (huf.source _ _ hs) (huf.words _ _ hs hm)
  have frame : ScanFrame s v := huf.trans hvf
  have h2v := frame.registers 2#5 (by decide)
  have h3v := frame.registers 3#5 (by decide)
  let ops := leftJoinOps (decide (sigWords words = 0)) (r (.GPR 3#5) v)
  let t := block base ops v
  have vpc : read_pc v = base + (if decide (sigWords words = 0) then 124#64 else 88#64) := by
    simpa only [sigWords, decide_eq_true_eq] using hvp
  have ht : run ops.length v = t := block_run base ops v
    (frame.code hc) (frame.error.trans he) (frame.aligned ha)
    (left_join_follows v base (decide (sigWords words = 0)) vpc)
  have htf : ScanFrame v t := scan_pure_frame base ops v
    (left_join_allowed (decide (sigWords words = 0)) (r (.GPR 3#5) v))
  refine ⟨3 + fuel + ops.length, t, ?_, frame.trans htf, ?_,
    (left_join_index v base _).trans hv9,
    (left_join_raw v base _).trans h2v, ?_⟩
  · rw [run_plus, run_plus, hu, hv, ht]
  · have count : r (.GPR 21#5) t =
        if decide (sigWords words = 0) then 0#64 else r (.GPR 10#5) v + 1#64 :=
      left_join_count v base (decide (sigWords words = 0))
    by_cases zero : sigWords words = 0
    · simpa [zero] using count
    · have scanned : r (.GPR 10#5) v = BitVec.ofNat 64 (sigWords words - 1) := hv10 zero
      have restore : BitVec.ofNat 64 (sigWords words - 1) + 1#64 =
          BitVec.ofNat 64 (sigWords words) := by
        arm_word_nf
        rw [← BitVec.ofNat_add, Nat.sub_add_cancel (show 1 ≤ sigWords words by omega)]
      simpa [zero, scanned, restore] using count
  · have pc : read_pc t = base + (if r (.GPR 3#5) v = 0#64 then 136#64 else 160#64) :=
      left_join_pc v base (decide (sigWords words = 0))
    exact pc.trans (congrArg (fun pointer : BitVec 64 =>
      base + (if pointer = 0#64 then 136#64 else 160#64)) h3v)

end SszArm.NatMul

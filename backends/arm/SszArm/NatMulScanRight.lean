import SszArm.NatMulScanRightStages

namespace SszArm.NatMul

open SszNative.Limbs

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
  have inputNonzero : r (.GPR 9#5) s ≠ 0#64 := by simpa only [h9] using nonzero
  have hu : run 3 s = u := block_run base [.p164, .p168, .p172] s hc he ha
    (right_head_follows s base hp inputNonzero)
  have huf : ScanFrame s u := scan_pure_frame base [.p164, .p168, .p172] s (by decide)
  obtain ⟨head8, head21, head9, head22, hup⟩ := right_head_values s base inputNonzero
  have hus := huf.source pointer words hs
  have hum := huf.words pointer words hs hm
  have hload : read_mem_bytes 8 (ScanLoad.right.address u)
      (NatCompare.saved u 11#5) = words[n]?.getD 0#64 := by
    have address : ScanLoad.right.address u = pointer + (BitVec.ofNat 64 n <<< 3) := by
      change r (.GPR 9#5) u - 8#64 = _
      rw [head9, h3, h9]
      bv_omega
    rw [address]
    exact NatCompare.limb_load u pointer words n 11#5 hn hus hum
  let v := scanLoadResult u base .right (words[n]?.getD 0#64)
  have hv : run 7 u = v := scan_load_run u base (words[n]?.getD 0#64) .right
    (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup hus.1 hload
  have hvf : ScanFrame s v :=
    huf.trans (scan_load_frame u base (words[n]?.getD 0#64) .right hus.1)
  have ht : run 2 v = block base [.p204, .p208] v :=
    block_run base [.p204, .p208] v (hvf.code hc) (hvf.error.trans he) (hvf.aligned ha)
      (right_tail_follows v base (scan_right_load_values u base (words[n]?.getD 0#64)).2.2.2.2)
  obtain ⟨out8, out21, out9, out22, outPC⟩ :=
    right_round_values s base (words[n]?.getD 0#64) inputNonzero
  refine ⟨?_, hvf.trans (scan_pure_frame base [.p204, .p208] v (by decide)),
    out8, out21, ?_, out22.trans h9, outPC⟩
  · rw [show 12 = 3 + 7 + 2 by decide, run_plus, run_plus, hu, hv, ht]
    rfl
  · rw [out9, h9]
    arm_word_nf
    rw [BitVec.ofNat_add, BitVec.add_sub_cancel]

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
    obtain ⟨zero8, zero21, zeroPC⟩ := right_zero_values s base (by simpa using h9)
    refine ⟨1, t, block_run base [.p164] s hc he ha ⟨hp, trivial⟩,
      scan_pure_frame base [.p164] s (by decide),
      zero8, zero21, ?_, ?_, ?_⟩
    · simp only [significantCount, ne_eq, not_true_eq_false, false_implies]
    · simp only [significantCount, ne_eq, not_true_eq_false, false_implies]
    · simpa only [significantCount, ↓reduceIte] using zeroPC
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
  have hu : run 1 s = u := block_run base [.p160] s hc he ha ⟨hp, trivial⟩
  have huf : ScanFrame s u := scan_pure_frame base [.p160] s (by decide)
  obtain ⟨entry8, entry21, entry9, hup⟩ := right_entry_values s base hp
  have hu9 : r (.GPR 9#5) u = BitVec.ofNat 64 words.length := entry9.trans h4
  obtain ⟨fuel, t, ht, htf, ht8, ht21, ht22, ht9, htp⟩ := right_scan base pointer words words.length u
    (Nat.le_refl _) (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup
    ((huf.registers 3#5 (by decide)).trans h3) hu9
    (huf.source _ _ hs) (huf.words _ _ hs hm)
  refine ⟨1 + fuel, t, ?_, huf.trans htf, ht8.trans entry8, ht21.trans entry21, ht22, ht9, htp⟩
  rw [run_plus, hu, ht]

end SszArm.NatMul

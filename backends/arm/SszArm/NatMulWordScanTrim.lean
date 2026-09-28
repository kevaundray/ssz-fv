import SszArm.NatMulWordScanArithmetic

namespace SszArm.NatMulWord

open UintCodec SszNative.Limbs


theorem trim_scan_round (s : ArmState) (base pointer bias : BitVec 64)
    (words : List (BitVec 64)) (n : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 252#64)
    (h1 : r (.GPR 1#5) s = pointer)
    (h2 : r (.GPR 2#5) s = BitVec.ofNat 64 words.length)
    (h8 : r (.GPR 8#5) s = bias - BitVec.ofNat 64 (8 * (n + 1)))
    (h9 : r (.GPR 9#5) s = BitVec.ofNat 64 (n + 1) - BitVec.ofNat 64 words.length)
    (h10 : r (.GPR 10#5) s = pointer + BitVec.ofNat 64 (8 * words.length) - 8#64)
    (hn : n < words.length) (hs : NatCompare.Source s pointer words)
    (hm : NatCompare.Words s pointer words) :
    let t := trimRound s base (words[n]?.getD 0#64)
    run 13 s = t ∧ ScanFrame s t ∧
      r (.GPR 1#5) t = pointer ∧ r (.GPR 2#5) t = BitVec.ofNat 64 words.length ∧
      r (.GPR 8#5) t = bias - BitVec.ofNat 64 (8 * n) ∧
      r (.GPR 9#5) t = BitVec.ofNat 64 n - BitVec.ofNat 64 words.length ∧
      r (.GPR 10#5) t = pointer + BitVec.ofNat 64 (8 * words.length) - 8#64 ∧
      read_pc t = if words[n]?.getD 0#64 = 0#64 then base + 252#64 else base + 304#64 := by
  have hbound : words.length < 2^64 := by have := hs.2.1; omega
  have hnonzero : BitVec.ofNat 64 (n + 1) ≠ 0#64 := by bv_omega
  let u := block base trimGuard s
  have hf := trim_guard_follows s base hp
  have hu : run 2 s = u := block_run base trimGuard s hc he ha hf
  have huf : ScanFrame s u := scan_pure_frame base trimGuard s (by decide)
  have huk (reg : BitVec 5) : r (.GPR reg) u = r (.GPR reg) s :=
    trim_guard_register s base reg
  have hup : read_pc u = base + 260#64 := by
    rw [trim_guard_pc, h2, h9, trim_remaining_sum, if_neg hnonzero]
  have hadd : LoadSite.trim.address u = pointer + (BitVec.ofNat 64 n <<< 3) := by
    change r (.GPR 10#5) u + (r (.GPR 9#5) u <<< 3) = _
    rw [huk, huk, h10, h9]
    exact trim_index_address pointer words.length n
  have hus := huf.source pointer words hs
  obtain ⟨physical, separate, valueAt⟩ :=
    scan_limb u pointer words n hn hus (huf.words pointer words hs hm)
  let v := loaded .trim u base (words[n]?.getD 0#64)
  have hv : run 8 u = v := load_run .trim u base _
    (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup hus.1
    (by simpa only [hadd] using physical) (by simpa only [hadd] using separate)
    (by simpa only [hadd] using valueAt)
  have hvf : ScanFrame s v :=
    huf.trans (scan_load_frame .trim u base (words[n]?.getD 0#64) (by decide) hus.1)
  have hvp : read_pc v = base + 292#64 := loaded_pc .trim u base (words[n]?.getD 0#64)
  have hvk (reg : BitVec 5) (hne : reg ≠ 11#5) : r (.GPR reg) v = r (.GPR reg) s :=
    (loaded_register .trim u base (words[n]?.getD 0#64) reg hne).trans (huk reg)
  have hv11 : r (.GPR 11#5) v = words[n]?.getD 0#64 :=
    loaded_value .trim u base (words[n]?.getD 0#64)
  have htail := trim_tail_follows v base hvp
  have ht : run 3 v = block base trimTail v :=
    block_run base trimTail v (hvf.code hc) (hvf.error.trans he) (hvf.aligned ha) htail
  refine ⟨?_, hvf.trans (scan_pure_frame base trimTail v (by decide)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 13 = 2 + 8 + 3 by decide, run_plus, run_plus, hu, hv, ht]
    rfl
  · change r (.GPR 1#5) (block base trimTail v) = pointer
    exact (trim_tail_keep v base 1#5 (by decide) (by decide)).trans ((hvk _ (by decide)).trans h1)
  · change r (.GPR 2#5) (block base trimTail v) = _
    exact (trim_tail_keep v base 2#5 (by decide) (by decide)).trans ((hvk _ (by decide)).trans h2)
  · change r (.GPR 8#5) (block base trimTail v) = _
    rw [trim_tail_offset, hvk 8#5 (by decide), h8]
    exact trim_offset_step bias n
  · change r (.GPR 9#5) (block base trimTail v) = _
    rw [trim_tail_index, hvk 9#5 (by decide), h9]
    exact trim_index_step words.length n
  · change r (.GPR 10#5) (block base trimTail v) = _
    exact (trim_tail_keep v base 10#5 (by decide) (by decide)).trans ((hvk _ (by decide)).trans h10)
  · change read_pc (block base trimTail v) = _
    rw [trim_tail_pc, hv11]

/-- The negative-index scan is well-founded on remaining physical words.
X2 remains the raw physical length, including every redundant high zero. -/
theorem trim_scan (base pointer bias : BitVec 64) (words : List (BitVec 64)) :
    ∀ n (s : ArmState), n ≤ words.length →
      CodeAt s base → read_err s = .None → CheckSPAlignment s →
      read_pc s = base + 252#64 → r (.GPR 1#5) s = pointer →
      r (.GPR 2#5) s = BitVec.ofNat 64 words.length →
      r (.GPR 8#5) s = bias - BitVec.ofNat 64 (8 * n) →
      r (.GPR 9#5) s = BitVec.ofNat 64 n - BitVec.ofNat 64 words.length →
      r (.GPR 10#5) s = pointer + BitVec.ofNat 64 (8 * words.length) - 8#64 →
      NatCompare.Source s pointer words → NatCompare.Words s pointer words →
      ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧
        r (.GPR 1#5) t = pointer ∧ r (.GPR 2#5) t = BitVec.ofNat 64 words.length ∧
        r (.GPR 8#5) t = bias - BitVec.ofNat 64 (8 * (significantCount words n - 1)) ∧
        r (.GPR 10#5) t = pointer + BitVec.ofNat 64 (8 * words.length) - 8#64 ∧
        read_pc t = (if significantCount words n = 0 then base + 920#64 else base + 304#64) ∧
        (significantCount words n ≠ 0 → r (.GPR 9#5) t =
          BitVec.ofNat 64 (significantCount words n - 1) - BitVec.ofNat 64 words.length) := by
  intro n
  induction n with
  | zero =>
    intro s hn hc he ha hp h1 h2 h8 h9 h10 hs hm
    let t := block base trimGuard s
    have hf := trim_guard_follows s base hp
    have hz : r (.GPR 2#5) s + r (.GPR 9#5) s = 0#64 := by
      rw [h2, h9, trim_remaining_sum]; rfl
    refine ⟨2, t, block_run base trimGuard s hc he ha hf,
      scan_pure_frame base trimGuard s (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (trim_guard_register s base 1#5).trans h1
    · exact (trim_guard_register s base 2#5).trans h2
    · exact (trim_guard_register s base 8#5).trans h8
    · exact (trim_guard_register s base 10#5).trans h10
    · change read_pc (block base trimGuard s) = base + 920#64
      rw [trim_guard_pc, if_pos hz]
    · intro h; exact False.elim (h rfl)
  | succ n ih =>
    intro s hn hc he ha hp h1 h2 h8 h9 h10 hs hm
    obtain ⟨hu, huf, hu1, hu2, hu8, hu9, hu10, hup⟩ :=
      trim_scan_round s base pointer bias words n hc he ha hp h1 h2 h8 h9 h10 (by omega) hs hm
    generalize stateEq : trimRound s base (words[n]?.getD 0#64) = u at
      hu huf hu1 hu2 hu8 hu9 hu10 hup
    by_cases hz : words[n]?.getD 0#64 = 0#64
    · obtain ⟨fuel, t, ht, htf, ht1, ht2, ht8, ht10, htp, ht9⟩ := ih u (by omega)
        (huf.code hc) (huf.error.trans he) (huf.aligned ha)
        (by simpa [hz] using hup) hu1 hu2 hu8 hu9 hu10
        (huf.source _ _ hs) (huf.words _ _ hs hm)
      refine ⟨13 + fuel, t, ?_, huf.trans htf, ht1, ht2, ?_, ht10, ?_, ?_⟩
      · rw [run_plus, hu, ht]
      · simpa [significantCount, hz] using ht8
      · simpa [significantCount, hz] using htp
      · simpa [significantCount, hz] using ht9
    · refine ⟨13, u, hu, huf, hu1, hu2, ?_, hu10, ?_, ?_⟩
      · simpa [significantCount, hz] using hu8
      · simpa [significantCount, hz] using hup
      · intro h; simpa [significantCount, hz] using hu9

end SszArm.NatMulWord

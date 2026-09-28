import SszArm.NatMulWordScanStages

namespace SszArm.NatMulWord

open UintCodec SszNative.Limbs


theorem identity_scan_round (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (n : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 108#64)
    (h1 : r (.GPR 1#5) s = pointer) (h9 : r (.GPR 9#5) s = BitVec.ofNat 64 n)
    (hn : n < words.length) (hs : NatCompare.Source s pointer words)
    (hm : NatCompare.Words s pointer words) :
    let t := identityRound s base (words[n]?.getD 0#64)
    run 13 s = t ∧ ScanFrame s t ∧
      r (.GPR 1#5) t = pointer ∧ r (.GPR 2#5) t = r (.GPR 2#5) s ∧
      r (.GPR 9#5) t = BitVec.ofNat 64 n - 1#64 ∧
      r (.GPR 8#5) t = BitVec.ofNat 64 n ∧
      read_pc t = if words[n]?.getD 0#64 = 0#64 then base + 108#64 else base + 160#64 := by
  have hbound : words.length < 2^64 := by have := hs.2.1; omega
  have hnonzero : BitVec.ofNat 64 n + 1#64 ≠ 0#64 := by bv_omega
  let u := block base identityGuard s
  have hf := identity_guard_follows s base hp
  have hu : run 2 s = u := block_run base identityGuard s hc he ha hf
  have huf : ScanFrame s u := scan_pure_frame base identityGuard s (by decide)
  have huk (reg : BitVec 5) : r (.GPR reg) u = r (.GPR reg) s :=
    identity_guard_register s base reg
  have hup : read_pc u = base + 116#64 := by
    rw [identity_guard_pc, h9, if_neg hnonzero]
  have hadd : LoadSite.identity.address u = pointer + (BitVec.ofNat 64 n <<< 3) := by
    change r (.GPR 1#5) u + (r (.GPR 9#5) u <<< 3) = _
    rw [huk, huk, h1, h9]
  have hus := huf.source pointer words hs
  obtain ⟨physical, separate, valueAt⟩ :=
    scan_limb u pointer words n hn hus (huf.words pointer words hs hm)
  let v := loaded .identity u base (words[n]?.getD 0#64)
  have hv : run 8 u = v := load_run .identity u base _
    (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup hus.1
    (by simpa only [hadd] using physical) (by simpa only [hadd] using separate)
    (by simpa only [hadd] using valueAt)
  have hvf : ScanFrame s v :=
    huf.trans (scan_load_frame .identity u base (words[n]?.getD 0#64) (by decide) hus.1)
  have hvp : read_pc v = base + 148#64 := loaded_pc .identity u base (words[n]?.getD 0#64)
  have hvk (reg : BitVec 5) (hne : reg ≠ 10#5) : r (.GPR reg) v = r (.GPR reg) s :=
    (loaded_register .identity u base (words[n]?.getD 0#64) reg hne).trans (huk reg)
  have hv10 : r (.GPR 10#5) v = words[n]?.getD 0#64 :=
    loaded_value .identity u base (words[n]?.getD 0#64)
  have htail := identity_tail_follows v base hvp
  have ht : run 3 v = block base identityTail v :=
    block_run base identityTail v (hvf.code hc) (hvf.error.trans he) (hvf.aligned ha) htail
  refine ⟨?_, hvf.trans (scan_pure_frame base identityTail v (by decide)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 13 = 2 + 8 + 3 by decide, run_plus, run_plus, hu, hv, ht]
    rfl
  · change r (.GPR 1#5) (block base identityTail v) = pointer
    exact (identity_tail_keep v base 1#5 (by decide) (by decide)).trans ((hvk _ (by decide)).trans h1)
  · change r (.GPR 2#5) (block base identityTail v) = r (.GPR 2#5) s
    exact (identity_tail_keep v base 2#5 (by decide) (by decide)).trans (hvk _ (by decide))
  · change r (.GPR 9#5) (block base identityTail v) = _
    rw [identity_tail_index, hvk 9#5 (by decide), h9]
  · change r (.GPR 8#5) (block base identityTail v) = _
    rw [identity_tail_count, hvk 9#5 (by decide), h9]
  · change read_pc (block base identityTail v) = _
    rw [identity_tail_pc, hv10]

/-- Induction is on the remaining physical list length, never on an external
fuel allowance. Empty Large and arbitrarily long redundant zero suffixes use
the same original branch at pc112. -/
theorem identity_scan (base pointer : BitVec 64) (words : List (BitVec 64)) :
    ∀ n (s : ArmState), n ≤ words.length →
      CodeAt s base → read_err s = .None → CheckSPAlignment s →
      read_pc s = base + 108#64 → r (.GPR 1#5) s = pointer →
      r (.GPR 9#5) s = BitVec.ofNat 64 n - 1#64 →
      NatCompare.Source s pointer words → NatCompare.Words s pointer words →
      ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧
        r (.GPR 1#5) t = pointer ∧ r (.GPR 2#5) t = r (.GPR 2#5) s ∧
        read_pc t = (if significantCount words n = 0 then base + 832#64 else base + 160#64) ∧
        (significantCount words n ≠ 0 →
          r (.GPR 8#5) t = BitVec.ofNat 64 (significantCount words n - 1)) := by
  intro n
  induction n with
  | zero =>
    intro s hn hc he ha hp h1 h9 hs hm
    let t := block base identityGuard s
    have hf := identity_guard_follows s base hp
    have hz : r (.GPR 9#5) s + 1#64 = 0#64 := by rw [h9]; decide
    refine ⟨2, t, block_run base identityGuard s hc he ha hf,
      scan_pure_frame base identityGuard s (by decide), ?_, ?_, ?_, ?_⟩
    · exact (identity_guard_register s base 1#5).trans h1
    · exact identity_guard_register s base 2#5
    · change read_pc (block base identityGuard s) = base + 832#64
      rw [identity_guard_pc, if_pos hz]
    · intro h; exact False.elim (h rfl)
  | succ n ih =>
    intro s hn hc he ha hp h1 h9 hs hm
    have h9' : r (.GPR 9#5) s = BitVec.ofNat 64 n := by
      simpa [BitVec.ofNat_add, BitVec.add_sub_cancel] using h9
    obtain ⟨hu, huf, hu1, hu2, hu9, hu8, hup⟩ :=
      identity_scan_round s base pointer words n hc he ha hp h1 h9' (by omega) hs hm
    generalize stateEq : identityRound s base (words[n]?.getD 0#64) = u at
      hu huf hu1 hu2 hu9 hu8 hup
    by_cases hz : words[n]?.getD 0#64 = 0#64
    · obtain ⟨fuel, t, ht, htf, ht1, ht2, htp, ht8⟩ := ih u (by omega)
        (huf.code hc) (huf.error.trans he) (huf.aligned ha)
        (by simpa [hz] using hup) hu1 hu9 (huf.source _ _ hs) (huf.words _ _ hs hm)
      refine ⟨13 + fuel, t, ?_, huf.trans htf, ht1, ht2.trans hu2, ?_, ?_⟩
      · rw [run_plus, hu, ht]
      · simpa [significantCount, hz] using htp
      · simpa [significantCount, hz] using ht8
    · refine ⟨13, u, hu, huf, hu1, hu2, ?_, ?_⟩
      · simpa [significantCount, hz] using hup
      · intro h; simpa [significantCount, hz] using hu8

end SszArm.NatMulWord

import SszArm.NatMulWordNormalizeStages

namespace SszArm.NatMulWord

open UintCodec SszNative.Limbs


/-- The post-indexed LDR reads the current highest word before moving X8 back.
Its premise is the current full physical image, not a future read oracle. -/
theorem normalize_scan_round (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (n : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1468#64)
    (h8 : r (.GPR 8#5) s = pointer + BitVec.ofNat 64 (8 * n))
    (h12 : r (.GPR 12#5) s = BitVec.ofNat 64 (n + 2))
    (hn : n < words.length) (hs : NatCompare.Source s pointer words)
    (hm : NatCompare.Words s pointer words) :
    let t := normalizeRound base s
    run 4 s = t ∧ NormalizeFrame s t ∧
      r (.GPR 8#5) t = pointer + BitVec.ofNat 64 (8 * n) - 8#64 ∧
      r (.GPR 9#5) t = words[n]?.getD 0#64 ∧
      r (.GPR 12#5) t = BitVec.ofNat 64 (n + 1) ∧
      read_pc t = if words[n]?.getD 0#64 = 0#64 then base + 1468#64 else base + 1484#64 := by
  have hbound := hs.2.1
  have hne : BitVec.ofNat 64 (n + 2) ≠ 1#64 := by bv_omega
  have hsub : BitVec.ofNat 64 (n + 2) - 1#64 = BitVec.ofNat 64 (n + 1) := by bv_omega
  have hload : read_mem_bytes 8 (pointer + BitVec.ofNat 64 (8 * n)) s =
      words[n]?.getD 0#64 := by
    have address : pointer + (BitVec.ofNat 64 n <<< 3) =
        pointer + BitVec.ofNat 64 (8 * n) := by bv_omega
    simpa only [address] using (scan_limb s pointer words n hn hs hm).2.2
  have hf := normalize_round_follows s base hp (by simpa only [h12] using hne)
  refine ⟨block_run base normalizeRoundOps s hc he ha hf,
    normalize_read_frame base normalizeRoundOps s (by decide), ?_, ?_, ?_, ?_⟩
  · rw [normalize_round_gpr]
    simp only [↓reduceIte, h8]
    bv_omega
  · rw [normalize_round_gpr]
    simp only [show (9#5 : BitVec 5) ≠ 8#5 by decide, ↓reduceIte, h8, hload]
  · rw [normalize_round_gpr]
    simp only [show (12#5 : BitVec 5) ≠ 8#5 by decide,
      show (12#5 : BitVec 5) ≠ 9#5 by decide, ↓reduceIte, h12, hsub]
  · rw [normalize_round_pc, h8, hload]

/-- The induction is over every remaining physical word. At zero no memory is
read, including when the post-indexed pointer has moved below the allocation. -/
theorem normalize_scan (base pointer : BitVec 64) (words : List (BitVec 64)) :
    ∀ n (s : ArmState), n ≤ words.length →
      CodeAt s base → read_err s = .None → CheckSPAlignment s →
      read_pc s = base + 1468#64 →
      (n ≠ 0 → r (.GPR 8#5) s = pointer + BitVec.ofNat 64 (8 * (n - 1))) →
      r (.GPR 12#5) s = BitVec.ofNat 64 (n + 1) →
      NatCompare.Source s pointer words → NatCompare.Words s pointer words →
      ∃ fuel t, run fuel s = t ∧ NormalizeFrame s t ∧
        read_pc t = (if significantCount words n = 0 then base + 1544#64 else base + 1484#64) ∧
        r (.GPR 12#5) t = BitVec.ofNat 64 (significantCount words n) ∧
        (significantCount words n = 0 → r (.GPR 9#5) t =
          if n = 0 then r (.GPR 9#5) s else 0#64) := by
  intro n
  induction n with
  | zero =>
    intro s hn hc he ha hp h8 h12 hs hm
    let t := block base normalizeGuard s
    have hf := normalize_guard_follows s base hp
    refine ⟨2, t, block_run base normalizeGuard s hc he ha hf,
      normalize_read_frame base normalizeGuard s (by decide), ?_, ?_, ?_⟩
    · change read_pc (block base normalizeGuard s) = _
      rw [normalize_guard_pc, h12]
      simp only [significantCount, Nat.zero_add, ↓reduceIte]
    · change r (.GPR 12#5) (block base normalizeGuard s) = _
      rw [normalize_guard_gpr, h12]
      simp only [significantCount, Nat.zero_add, ↓reduceIte, BitVec.sub_self]
    · intro zero
      change r (.GPR 9#5) (block base normalizeGuard s) = _
      rw [normalize_guard_gpr]
      simp only [show (9#5 : BitVec 5) ≠ 12#5 by decide, ↓reduceIte]
  | succ n ih =>
    intro s hn hc he ha hp h8 h12 hs hm
    obtain ⟨hu, huf, hu8, hu9, hu12, hup⟩ := normalize_scan_round s base pointer words n
      hc he ha hp (by simpa using h8 (by omega)) (by simpa [Nat.add_assoc] using h12)
      (by omega) hs hm
    let u := normalizeRound base s
    change run 4 s = u at hu
    change NormalizeFrame s u at huf
    change r (.GPR 8#5) u = pointer + BitVec.ofNat 64 (8 * n) - 8#64 at hu8
    change r (.GPR 9#5) u = words[n]?.getD 0#64 at hu9
    change r (.GPR 12#5) u = BitVec.ofNat 64 (n + 1) at hu12
    change read_pc u = if words[n]?.getD 0#64 = 0#64 then base + 1468#64 else base + 1484#64 at hup
    by_cases hz : words[n]?.getD 0#64 = 0#64
    · have next8 : n ≠ 0 → r (.GPR 8#5) u = pointer + BitVec.ofNat 64 (8 * (n - 1)) := by
        intro positive
        rw [hu8]
        bv_omega
      obtain ⟨fuel, t, ht, htf, htp, ht12, ht9⟩ := ih u (by omega)
        (huf.code hc) (huf.error.trans he) (huf.aligned ha)
        (by simpa [hz] using hup) next8 hu12 (huf.source _ _ hs) (huf.words _ _ hm)
      refine ⟨4 + fuel, t, ?_, huf.trans htf, ?_, ?_, ?_⟩
      · rw [run_plus, hu, ht]
      · simpa [significantCount, hz] using htp
      · simpa [significantCount, hz] using ht12
      · intro zero
        have count : significantCount words n = 0 := by simpa [significantCount, hz] using zero
        simpa [hu9, hz] using ht9 count
    · refine ⟨4, u, hu, huf, ?_, ?_, ?_⟩
      · simpa [significantCount, hz] using hup
      · simpa [significantCount, hz] using hu12
      · simp [significantCount, hz]

end SszArm.NatMulWord

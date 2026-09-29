import SszArm.NatMulWordIdentityStages
import SszNatOperandNormalization

namespace SszArm.NatMulWord

open UintCodec SszNative.Limbs

theorem normalized_zero (pointer : BitVec 64) (words : List (BitVec 64))
    (hz : sigWords words = 0) : SszNative.NatOperand.fromWords pointer words = .small 0#64 := by
  have hlen : (trim words).length = 0 := (trim_length words).trans hz
  have hnil := List.eq_nil_of_length_eq_zero hlen
  simp [SszNative.NatOperand.fromWords, hnil]

/-- The nonzero scan exit performs the native one-word canonicalization, not
an assumed canonicality of the input list. -/
theorem identity_normalize_exit (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 160#64)
    (h1 : r (.GPR 1#5) s = pointer)
    (h8 : r (.GPR 8#5) s = BitVec.ofNat 64 (sigWords words - 1))
    (hn : sigWords words ≠ 0)
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧ read_pc t = base + 180#64 ∧
      r (.GPR 1#5) t = (SszNative.NatOperand.fromWords pointer words).pointer ∧
      r (.GPR 2#5) t = (SszNative.NatOperand.fromWords pointer words).payload := by
  have hbound : sigWords words < 2^64 := by
    have := hs.2.1
    have := sigWords_le_length words
    omega
  have hadd : BitVec.ofNat 64 (sigWords words - 1) + 1#64 = BitVec.ofNat 64 (sigWords words) := by
    bv_omega
  have countNeOne (hne : sigWords words ≠ 1) :
      BitVec.ofNat 64 (sigWords words) ≠ 1#64 := by bv_omega
  let u := block base identityCountOps s
  have hu : run 3 s = u := block_run base identityCountOps s hc he ha
    (identity_count_follows s base hp)
  have huf : ScanFrame s u := scan_pure_frame base identityCountOps s (by decide)
  have hu1 : r (.GPR 1#5) u = pointer := (identity_count_pointer s base).trans h1
  have hu2 : r (.GPR 2#5) u = BitVec.ofNat 64 (sigWords words) := by
    rw [identity_count_payload, h8, hadd]
  have hup : read_pc u =
      if BitVec.ofNat 64 (sigWords words) = 1#64 then base + 172#64 else base + 180#64 := by
    rw [identity_count_pc, h8, hadd]
  by_cases hone : sigWords words = 1
  · have hpositive : 0 < words.length := by have := sigWords_le_length words; omega
    have hu172 : read_pc u = base + 172#64 := by
      simpa only [hone, BitVec.ofNat_eq_ofNat, ↓reduceIte] using hup
    have hword : read_mem_bytes 8 pointer u = words[0]?.getD 0#64 := by
      simpa only [show (BitVec.ofNat 64 0 <<< 3) = 0#64 from rfl, BitVec.add_zero] using
        (scan_limb u pointer words 0 hpositive (huf.source _ _ hs) (huf.words _ _ hs hm)).2.2
    let t := block base identityCanonOps u
    have ht : run 2 u = t := block_run base identityCanonOps u
      (huf.code hc) (huf.error.trans he) (huf.aligned ha) (identity_canon_follows u base hu172)
    refine ⟨3 + 2, t, ?_, huf.trans (scan_pure_frame base identityCanonOps u (by decide)),
      identity_canon_pc u base hu172, ?_, ?_⟩
    · rw [run_plus, hu, ht]
    · rw [identity_canon_pointer, SszNative.NatOperand.fromWords_pointer, hone]
      rfl
    · rw [identity_canon_payload, hu1, hword, SszNative.NatOperand.fromWords_payload, hone]
      rfl
  · have hgt : ¬ sigWords words ≤ 1 := by omega
    have hne := countNeOne hone
    refine ⟨3, u, hu, huf, ?_, ?_, ?_⟩
    · simpa only [if_neg hne] using hup
    · simpa only [SszNative.NatOperand.fromWords_pointer, if_neg hgt] using hu1
    · simpa only [SszNative.NatOperand.fromWords_payload, if_neg hgt] using hu2

/-- Exact two native return-body entrances selected by factor-one. -/
def IdentityReady (base : BitVec 64) (operand : SszNative.NatOperand) (t : ArmState) : Prop :=
  (read_pc t = base + 832#64 ∧ operand.normalized = .small 0#64) ∨
  (read_pc t = base + 180#64 ∧ r (.GPR 1#5) t = operand.normalized.pointer ∧
    r (.GPR 2#5) t = operand.normalized.payload)

theorem identity_large (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 100#64) (hn : pointer ≠ 0#64)
    (h1 : r (.GPR 1#5) s = pointer)
    (h2 : r (.GPR 2#5) s = BitVec.ofNat 64 words.length)
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧ IdentityReady base (.large pointer words) t := by
  let u := block base identityInitOps s
  have nonzero : r (.GPR 1#5) s ≠ 0#64 := by rw [h1]; exact hn
  have hu : run 2 s = u := block_run base identityInitOps s hc he ha
    (identity_init_follows s base hp nonzero)
  have huf : ScanFrame s u := scan_pure_frame base identityInitOps s (by decide)
  have hup : read_pc u = base + 108#64 := identity_init_pc s base nonzero
  have hu1 : r (.GPR 1#5) u = pointer := (identity_init_pointer s base).trans h1
  have hu9 : r (.GPR 9#5) u = BitVec.ofNat 64 words.length - 1#64 := by
    rw [identity_init_index, h2]
  obtain ⟨fuel, t, ht, htf, ht1, ht2, htp, ht8⟩ := identity_scan base pointer words words.length u
    (Nat.le_refl _) (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup hu1 hu9
    (huf.source _ _ hs) (huf.words _ _ hs hm)
  have hst := huf.trans htf
  change read_pc t = (if sigWords words = 0 then base + 832#64 else base + 160#64) at htp
  change sigWords words ≠ 0 → r (.GPR 8#5) t = BitVec.ofNat 64 (sigWords words - 1) at ht8
  by_cases hz : sigWords words = 0
  · refine ⟨2 + fuel, t, ?_, hst, Or.inl ⟨by simpa [hz] using htp, ?_⟩⟩
    · rw [run_plus, hu, ht]
    · exact normalized_zero pointer words hz
  · obtain ⟨extra, v, hv, hvf, hvp, hv1, hv2⟩ := identity_normalize_exit t base pointer words
      (hst.code hc) (hst.error.trans he) (hst.aligned ha) (by simpa [hz] using htp)
      ht1 (ht8 hz) hz (hst.source _ _ hs) (hst.words _ _ hs hm)
    refine ⟨2 + fuel + extra, v, ?_, hst.trans hvf, Or.inr ⟨hvp, hv1, hv2⟩⟩
    rw [run_plus, run_plus, hu, ht, hv]

end SszArm.NatMulWord

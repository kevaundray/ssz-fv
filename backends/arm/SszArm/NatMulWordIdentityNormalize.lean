import SszArm.NatMulWordIdentityScan
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
  have hpc : r .PC s = base + 160#64 := hp
  by_cases hone : sigWords words = 1
  · have hpositive : 0 < words.length := by have := sigWords_le_length words; omega
    have hword : read_mem_bytes 8 pointer s = words[0]?.getD 0#64 := by
      simpa using (scan_limb s pointer words 0 hpositive hs hm).2.2
    let ops : List Op := [.p160, .p164, .p168, .p172, .p176]
    let t := block base ops s
    have hf : Follows base ops s := by
      simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
        hpc, h8, hone, BitVec.add_assoc]
    refine ⟨5, t, block_run base ops s hc he ha hf,
      scan_pure_frame base ops s (by decide), ?_, ?_, ?_⟩
    all_goals simp [t, ops, block, Op.effect, put, next, state_simp_rules,
      hpc, h8, hone, h1, hword, BitVec.add_assoc,
      SszNative.NatOperand.fromWords_pointer, SszNative.NatOperand.fromWords_payload]
  · have hgt : ¬ sigWords words ≤ 1 := by omega
    have hne : BitVec.ofNat 64 (sigWords words) ≠ 1#64 := by bv_omega
    let ops : List Op := [.p160, .p164, .p168]
    let t := block base ops s
    have hf : Follows base ops s := by
      simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
        hpc, h8, hadd, hne, BitVec.add_assoc]
    refine ⟨3, t, block_run base ops s hc he ha hf,
      scan_pure_frame base ops s (by decide), ?_, ?_, ?_⟩
    all_goals simp [t, ops, block, Op.effect, put, next, state_simp_rules,
      hpc, h8, hadd, hne, h1, BitVec.add_assoc,
      SszNative.NatOperand.fromWords_pointer, SszNative.NatOperand.fromWords_payload, hgt]

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
  let ops : List Op := [.p100, .p104]
  let u := block base ops s
  have hpc : r .PC s = base + 100#64 := hp
  have hf : Follows base ops s := by
    simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
      hpc, h1, hn, BitVec.add_assoc]
  have hu : run 2 s = u := block_run base ops s hc he ha hf
  have huf := scan_pure_frame base ops s (by decide)
  have hup : read_pc u = base + 108#64 := by
    simp [u, ops, block, Op.effect, put, next, state_simp_rules, h1, hn, BitVec.add_assoc]
  have hu1 : r (.GPR 1#5) u = pointer := by
    simp [u, ops, block, Op.effect, put, next, state_simp_rules, h1]
  have hu9 : r (.GPR 9#5) u = BitVec.ofNat 64 words.length - 1#64 := by
    simp [u, ops, block, Op.effect, put, next, state_simp_rules, h2]
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

import SszArm.NatMulNormalizeScan
import SszArm.NatMulWordIdentityNormalize

namespace SszArm.NatMul

open UintCodec SszNative.Limbs

theorem normalize_nonzero_exit (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1276#64) (h20 : r (.GPR 20#5) s = pointer)
    (h8 : r (.GPR 8#5) s = BitVec.ofNat 64 (sigWords words - 1))
    (hn : sigWords words ≠ 0)
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    ∃ fuel t, run fuel s = t ∧ NormalizeFrame s t ∧ read_pc t = base + 1296#64 ∧
      r (.GPR 20#5) t = (SszNative.NatOperand.fromWords pointer words).pointer ∧
      r (.GPR 8#5) t = (SszNative.NatOperand.fromWords pointer words).payload := by
  have hbound : sigWords words < 2^64 := by
    have := hs.2.1
    have := sigWords_le_length words
    omega
  have hadd : BitVec.ofNat 64 (sigWords words - 1) + 1#64 = BitVec.ofNat 64 (sigWords words) := by
    bv_omega
  have hpc : r .PC s = base + 1276#64 := hp
  by_cases hone : sigWords words = 1
  · have hpositive : 0 < words.length := by have := sigWords_le_length words; omega
    have hword : read_mem_bytes 8 pointer s = words[0]?.getD 0#64 := by
      simpa using (NatMulWord.scan_limb s pointer words 0 hpositive hs hm).2.2
    let ops : List Op := [.p1276, .p1280, .p1284, .p1288, .p1292]
    let t := block base ops s
    have hf : Follows base ops s := by
      simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
        hpc, h8, hone, BitVec.add_assoc]
    refine ⟨5, t, block_run base ops s hc he ha hf,
      normalize_pure_frame base ops s (by decide), ?_, ?_, ?_⟩
    all_goals simp [t, ops, block, Op.effect, put, next, state_simp_rules,
      hpc, h8, hone, h20, hword, BitVec.add_assoc,
      SszNative.NatOperand.fromWords_pointer, SszNative.NatOperand.fromWords_payload]
  · have hgt : ¬ sigWords words ≤ 1 := by omega
    have hne : BitVec.ofNat 64 (sigWords words) ≠ 1#64 := by bv_omega
    let ops : List Op := [.p1276, .p1280, .p1284]
    let t := block base ops s
    have hf : Follows base ops s := by
      simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
        hpc, h8, hadd, hne, BitVec.add_assoc]
    refine ⟨3, t, block_run base ops s hc he ha hf,
      normalize_pure_frame base ops s (by decide), ?_, ?_, ?_⟩
    all_goals simp [t, ops, block, Op.effect, put, next, state_simp_rules,
      hpc, h8, hadd, hne, h20, BitVec.add_assoc,
      SszNative.NatOperand.fromWords_pointer, SszNative.NatOperand.fromWords_payload, hgt]

theorem normalize_ready (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1060#64) (h20 : r (.GPR 20#5) s = pointer)
    (h23 : r (.GPR 23#5) s = BitVec.ofNat 64 words.length - 1#64)
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    ∃ fuel t, run fuel s = t ∧ NormalizeFrame s t ∧ read_pc t = base + 1296#64 ∧
      r (.GPR 20#5) t = (SszNative.NatOperand.fromWords pointer words).pointer ∧
      r (.GPR 8#5) t = (SszNative.NatOperand.fromWords pointer words).payload := by
  obtain ⟨fuel, u, hu, huf, hu20, hup, hu8⟩ :=
    normalize_scan base pointer words words.length s (Nat.le_refl _) hc he ha hp h20 h23 hs hm
  change read_pc u = (if sigWords words = 0 then base + 1068#64 else base + 1276#64) at hup
  change sigWords words ≠ 0 → r (.GPR 8#5) u = BitVec.ofNat 64 (sigWords words - 1) at hu8
  by_cases hz : sigWords words = 0
  · have hpc : r .PC u = base + 1068#64 := by simpa [hz] using hup
    let ops : List Op := [.p1068, .p1072, .p1292]
    let t := block base ops u
    have hf : Follows base ops u := by
      simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]
    have ht : run 3 u = t := block_run base ops u (huf.code hc) (huf.error.trans he) (huf.aligned ha) hf
    refine ⟨fuel + 3, t, ?_, huf.trans (normalize_pure_frame base ops u (by decide)), ?_, ?_, ?_⟩
    · rw [run_plus, hu, ht]
    all_goals simp [t, ops, block, Op.effect, put, next, state_simp_rules,
      NatMulWord.normalized_zero pointer words hz, SszNative.NatOperand.pointer,
      SszNative.NatOperand.payload, BitVec.add_assoc]
  · obtain ⟨extra, t, ht, htf, htp, ht20, ht8⟩ := normalize_nonzero_exit u base pointer words
      (huf.code hc) (huf.error.trans he) (huf.aligned ha) (by simpa [hz] using hup)
      hu20 (hu8 hz) hz (huf.source _ _ hs) (huf.words _ _ hs hm)
    refine ⟨fuel + extra, t, ?_, huf.trans htf, htp, ht20, ht8⟩
    rw [run_plus, hu, ht]

end SszArm.NatMul

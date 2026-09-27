import SszArm.NatDivisionScan
import SszNatOperandNormalization

namespace SszArm.NatDivision

open UintCodec SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private theorem normalized_zero (pointer : BitVec 64) (words : List (BitVec 64))
    (hz : sigWords words = 0) : SszNative.NatOperand.fromWords pointer words = .small 0#64 := by
  have hlen : (trim words).length = 0 := (trim_length words).trans hz
  have hnil := List.eq_nil_of_length_eq_zero hlen
  simp [SszNative.NatOperand.fromWords, hnil]

/-- The quotient scan's three native exits implement empty/single/multiword
normalization without changing the stored quotient array. -/
theorem normalization_exit (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 (scanExit true (sigWords words)))
    (h24 : r (.GPR 24#5) s = pointer)
    (h8 : sigWords words ≠ 0 → r (.GPR 8#5) s = BitVec.ofNat 64 (sigWords words - 1))
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧ read_pc t = base + 1120#64 ∧
      r (.GPR 8#5) t = 0#64 ∧
      r (.GPR 24#5) t = (SszNative.NatOperand.fromWords pointer words).pointer ∧
      r (.GPR 10#5) t = (SszNative.NatOperand.fromWords pointer words).payload := by
  by_cases hz : sigWords words = 0
  · let ops : List Op := [.p1108, .p1112, .p1116]
    let t := block base ops s
    have hpc : r .PC s = base + 1108#64 := by
      change read_pc s = base + 1108#64
      simpa [scanExit, hz] using hp
    have hf : Follows base ops s := by
      simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]
    refine ⟨3, t, block_run base ops s hc he ha hf,
      scan_pure_frame base ops s (by decide), ?_, ?_, ?_, ?_⟩
    all_goals simp [t, ops, block, Op.effect, put, next, state_simp_rules,
      hpc, BitVec.add_assoc, normalized_zero pointer words hz,
      SszNative.NatOperand.pointer, SszNative.NatOperand.payload]
  · have hpc : r .PC s = base + 1088#64 := by
      change read_pc s = base + 1088#64
      simpa [scanExit, hz] using hp
    have hcount := h8 hz
    have hbound : sigWords words < 2^64 := by
      have := hs.2.1
      have := sigWords_le_length words
      omega
    have hadd : BitVec.ofNat 64 (sigWords words - 1) + 1#64 =
        BitVec.ofNat 64 (sigWords words) := by bv_omega
    by_cases hone : sigWords words = 1
    · have hpositive : 0 < words.length := by have := sigWords_le_length words; omega
      have hword : read_mem_bytes 8 pointer s = words[0]?.getD 0#64 := by
        have h := hm ⟨0, hpositive⟩
        simpa [List.getElem?_eq_getElem hpositive] using h
      let ops : List Op := [.p1088, .p1092, .p1096, .p1100, .p1104, .p1112, .p1116]
      let t := block base ops s
      have hf : Follows base ops s := by
        simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
          hpc, hcount, hone, BitVec.add_assoc]
      refine ⟨7, t, block_run base ops s hc he ha hf,
        scan_pure_frame base ops s (by decide), ?_, ?_, ?_, ?_⟩
      all_goals simp [t, ops, block, Op.effect, put, next, state_simp_rules,
        hpc, hcount, hone, h24, hword, BitVec.add_assoc,
        SszNative.NatOperand.fromWords_pointer, SszNative.NatOperand.fromWords_payload]
    · have hgt : 1 < sigWords words := by omega
      have hne : BitVec.ofNat 64 (sigWords words) ≠ 1#64 := by bv_omega
      let ops : List Op := [.p1088, .p1092, .p1096, .p1116]
      let t := block base ops s
      have hf : Follows base ops s := by
        simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
          hpc, hcount, hadd, hne, BitVec.add_assoc]
      refine ⟨4, t, block_run base ops s hc he ha hf,
        scan_pure_frame base ops s (by decide), ?_, ?_, ?_, ?_⟩
      all_goals simp [t, ops, block, Op.effect, put, next, state_simp_rules,
        hpc, hcount, hadd, hne, h24, BitVec.add_assoc,
        SszNative.NatOperand.fromWords_pointer, SszNative.NatOperand.fromWords_payload,
        show ¬ sigWords words ≤ 1 by omega]

/-- Native pc1032 through the normalization exit. The scratch list is the full
physical quotient list; redundant zero words remain present in memory. -/
theorem quotient_normalization (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1032#64)
    (h24 : r (.GPR 24#5) s = pointer)
    (h22 : r (.GPR 22#5) s = BitVec.ofNat 64 (words.length + 1))
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    ∃ fuel u, run fuel s = u ∧ ScanFrame s u ∧ read_pc u = base + 1120#64 ∧
      r (.GPR 8#5) u = 0#64 ∧
      r (.GPR 24#5) u = (SszNative.NatOperand.fromWords pointer words).pointer ∧
      r (.GPR 10#5) u = (SszNative.NatOperand.fromWords pointer words).payload := by
  let v := Op.p1032.effect base s
  have hv : run 1 s = v := by
    change stepi s = v
    exact step s base .p1032 hc hp he ha
  have hvf : ScanFrame s v := scan_pure_frame base [.p1032] s (by decide)
  have hpc0 : r .PC s = base + 1032#64 := hp
  have hvp : read_pc v = base + 1036#64 := by
    simp [v, Op.effect, put, next, state_simp_rules, hpc0, BitVec.add_assoc]
  have hv24 : r (.GPR 24#5) v = pointer := by
    simpa [v, Op.effect, put, next, state_simp_rules] using h24
  have hv9 : r (.GPR 9#5) v = BitVec.ofNat 64 words.length - 1#64 := by
    simp [v, Op.effect, put, next, state_simp_rules, h22, BitVec.ofNat_add]
    bv_omega
  obtain ⟨fuel, t, ht, htf, htkeep, htp, ht8⟩ := significant_scan base pointer words true
    words.length v (Nat.le_refl _) (hvf.code hc) (hvf.error.trans he) (hvf.aligned ha)
    hvp hv24 hv9 (hvf.source _ _ hs) (hvf.words _ _ hs hm)
  have hst := hvf.trans htf
  obtain ⟨extra, u, hu, huf, hup, hu8, hu24, hu10⟩ := normalization_exit t base pointer words
    (hst.code hc) (hst.error.trans he) (hst.aligned ha) htp
    ((htkeep 24#5 (by decide)).trans hv24) ht8
    (hst.source _ _ hs) (hst.words _ _ hs hm)
  refine ⟨1 + fuel + extra, u, ?_, hst.trans huf, hup, hu8, hu24, hu10⟩
  rw [run_plus, run_plus, hv, ht, hu]

/-- The final two normalization instructions store the selected pointer and
branch to the shared payload/remainder return path. This retains an exact state
expression, hence every byte except the eight output bytes is unchanged. -/
theorem quotient_normalization_store (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1120#64) :
    run 2 s = w .PC (base + 800#64)
      (write_mem_bytes 8 (r (.GPR 19#5) s) (r (.GPR 24#5) s) s) := by
  have hpc : r .PC s = base + 1120#64 := hp
  have hf : Follows base [.p1120, .p1124] s := by
    simp [Follows, Op.row, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]
  rw [show 2 = ([Op.p1120, .p1124] : List Op).length by rfl,
    block_run base [.p1120, .p1124] s hc he ha hf]
  simp [block, Op.effect, next, state_simp_rules]

/-- Full pc1032..1124 normalization, exposing the sole output store separately
from the scan's protected-memory frame. -/
theorem quotient_normalization_full (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1032#64)
    (h24 : r (.GPR 24#5) s = pointer)
    (h22 : r (.GPR 22#5) s = BitVec.ofNat 64 (words.length + 1))
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    ∃ fuel u, run (fuel + 2) s = w .PC (base + 800#64)
        (write_mem_bytes 8 (r (.GPR 19#5) s)
          (SszNative.NatOperand.fromWords pointer words).pointer u) ∧
      ScanFrame s u ∧ r (.GPR 8#5) u = 0#64 ∧
      r (.GPR 24#5) u = (SszNative.NatOperand.fromWords pointer words).pointer ∧
      r (.GPR 10#5) u = (SszNative.NatOperand.fromWords pointer words).payload := by
  obtain ⟨fuel, u, hu, huf, hup, hu8, hu24, hu10⟩ :=
    quotient_normalization s base pointer words hc he ha hp h24 h22 hs hm
  refine ⟨fuel, u, ?_, huf, hu8, hu24, hu10⟩
  rw [run_plus, hu, quotient_normalization_store u base
    (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup,
    huf.registers 19#5 (by decide), hu24]

end SszArm.NatDivision

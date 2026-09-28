import SszArm.NatMulWordScanTrim
import SszArm.NatMulWordIdentityNormalize
import SszArm.NatMulWordContract

namespace SszArm.NatMulWord

open UintCodec SszNative.Limbs

/-- The original compare/branch dispatch gives factor-one precedence over the
factor-zero and general multiplication paths. -/
theorem word_dispatch (s : ArmState) (base factor : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base) (h3 : r (.GPR 3#5) s = factor) :
    ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧
      (∀ reg : BitVec 5, r (.GPR reg) t = r (.GPR reg) s) ∧
      read_pc t = (if factor = 1#64 then base + 100#64
        else if factor = 0#64 then base + 12#64 else base + 228#64) := by
  have hpc : r .PC s = base := hp
  by_cases hone : factor = 1#64
  · let ops : List Op := [.p0, .p4]
    let t := block base ops s
    have hf : Follows base ops s := by
      simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]
    refine ⟨2, t, block_run base ops s hc he ha hf,
      scan_pure_frame base ops s (by decide), ?_, ?_⟩
    · intro reg
      simp [t, ops, block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
    · simp [t, ops, block, Op.effect, put, next, state_simp_rules, h3, hone]
  · let ops : List Op := [.p0, .p4, .p8]
    let t := block base ops s
    have hf : Follows base ops s := by
      simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
        hpc, h3, hone, BitVec.add_assoc]
    refine ⟨3, t, block_run base ops s hc he ha hf,
      scan_pure_frame base ops s (by decide), ?_, ?_⟩
    · intro reg
      simp [t, ops, block, Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
    · by_cases hz : factor = 0#64 <;>
        simp [t, ops, block, Op.effect, put, next, state_simp_rules, h3, hone, hz]

/-- X8 is exposed exactly, retaining the original xor lowering without imposing
an additional logical size bound or hiding its modular arithmetic. -/
def trimBias (words : List (BitVec 64)) : BitVec 64 :=
  ((BitVec.ofNat 64 words.length <<< 3) ^^^ 18446744073709551608#64) +
    BitVec.ofNat 64 (8 * words.length)

theorem trim_scan_entry (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 228#64) (hn : pointer ≠ 0#64)
    (h1 : r (.GPR 1#5) s = pointer)
    (h2 : r (.GPR 2#5) s = BitVec.ofNat 64 words.length)
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧
      r (.GPR 1#5) t = pointer ∧ r (.GPR 2#5) t = BitVec.ofNat 64 words.length ∧
      r (.GPR 8#5) t = trimBias words - BitVec.ofNat 64 (8 * (sigWords words - 1)) ∧
      read_pc t = (if sigWords words = 0 then base + 920#64 else base + 304#64) ∧
      (sigWords words ≠ 0 → r (.GPR 9#5) t =
        BitVec.ofNat 64 (sigWords words - 1) - BitVec.ofNat 64 words.length) := by
  let ops : List Op := [.p228, .p232, .p236, .p240, .p244, .p248]
  let u := block base ops s
  have hpc : r .PC s = base + 228#64 := hp
  have hf : Follows base ops s := by
    simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
      hpc, h1, hn, BitVec.add_assoc]
  have hu : run 6 s = u := block_run base ops s hc he ha hf
  have huf := scan_pure_frame base ops s (by decide)
  have hup : read_pc u = base + 252#64 := by
    simp [u, ops, block, Op.effect, put, next, state_simp_rules, h1, hn, BitVec.add_assoc]
  have hu1 : r (.GPR 1#5) u = pointer := by
    simp [u, ops, block, Op.effect, put, next, state_simp_rules, h1]
  have hu2 : r (.GPR 2#5) u = BitVec.ofNat 64 words.length := by
    simp [u, ops, block, Op.effect, put, next, state_simp_rules, h2]
  have hu8 : r (.GPR 8#5) u = trimBias words - BitVec.ofNat 64 (8 * words.length) := by
    simp [u, ops, trimBias, block, Op.effect, put, next, state_simp_rules, h2]
  have hu9 : r (.GPR 9#5) u = BitVec.ofNat 64 words.length - BitVec.ofNat 64 words.length := by
    simp [u, ops, block, Op.effect, put, next, state_simp_rules]
  have hu10 : r (.GPR 10#5) u = pointer + BitVec.ofNat 64 (8 * words.length) - 8#64 := by
    simp [u, ops, block, Op.effect, put, next, state_simp_rules, h1, h2]
    bv_omega
  obtain ⟨fuel, t, ht, htf, ht1, ht2, ht8, ht10, htp, ht9⟩ :=
    trim_scan base pointer (trimBias words) words words.length u (Nat.le_refl _)
      (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup hu1 hu2 hu8 hu9 hu10
      (huf.source _ _ hs) (huf.words _ _ hs hm)
  refine ⟨6 + fuel, t, ?_, huf.trans htf, ht1, ht2, ht8, htp, ht9⟩
  rw [run_plus, hu, ht]

/-- The scan's empty/single/multiword exits preserve the raw physical input and
select either original low-word multiplication or the reservation guard. -/
theorem trim_normalize_exit (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = (if sigWords words = 0 then base + 920#64 else base + 304#64))
    (h1 : r (.GPR 1#5) s = pointer)
    (h2 : r (.GPR 2#5) s = BitVec.ofNat 64 words.length)
    (h9 : sigWords words ≠ 0 → r (.GPR 9#5) s =
      BitVec.ofNat 64 (sigWords words - 1) - BitVec.ofNat 64 words.length)
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧ r (.GPR 1#5) t = pointer ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧
      (if sigWords words ≤ 1 then
        read_pc t = base + 928#64 ∧ r (.GPR 2#5) t = words[0]?.getD 0#64
       else read_pc t = base + 320#64 ∧ r (.GPR 2#5) t = BitVec.ofNat 64 words.length ∧
        r (.GPR 9#5) t = BitVec.ofNat 64 (sigWords words) ∧
        r (.GPR 12#5) t = BitVec.ofNat 64 (sigWords words - 1)) := by
  have hlength : words.length < 2^64 := by have := hs.2.1; omega
  have hbound : sigWords words < 2^64 := Nat.lt_of_le_of_lt (sigWords_le_length words) hlength
  by_cases hz : sigWords words = 0
  · have hpc : r .PC s = base + 920#64 := by simpa [hz] using hp
    by_cases hempty : words = []
    · let ops : List Op := [.p920]
      let t := block base ops s
      have hf : Follows base ops s := by simp [ops, Follows, Op.row, hpc]
      refine ⟨1, t, block_run base ops s hc he ha hf,
        scan_pure_frame base ops s (by decide), ?_, ?_, ?_⟩
      all_goals simp [t, ops, block, Op.effect, put, next, state_simp_rules, h1, h2, hempty, hz]
    · have hpositive : 0 < words.length := List.length_pos_iff.mpr hempty
      have hnonzero : BitVec.ofNat 64 words.length ≠ 0#64 := by bv_omega
      have hword : read_mem_bytes 8 pointer s = words[0]?.getD 0#64 := by
        simpa using (scan_limb s pointer words 0 hpositive hs hm).2.2
      let ops : List Op := [.p920, .p924]
      let t := block base ops s
      have hf : Follows base ops s := by
        simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
          hpc, h2, hnonzero, BitVec.add_assoc]
      refine ⟨2, t, block_run base ops s hc he ha hf,
        scan_pure_frame base ops s (by decide), ?_, ?_, ?_⟩
      all_goals simp [t, ops, block, Op.effect, put, next, state_simp_rules,
        hpc, h1, h2, hnonzero, hword, hz, BitVec.add_assoc]
  · have hpc : r .PC s = base + 304#64 := by simpa [hz] using hp
    have hcount := h9 hz
    have hsum : BitVec.ofNat 64 words.length +
        (BitVec.ofNat 64 (sigWords words - 1) - BitVec.ofNat 64 words.length) =
        BitVec.ofNat 64 (sigWords words - 1) := by bv_omega
    have hadd : BitVec.ofNat 64 (sigWords words - 1) + 1#64 =
        BitVec.ofNat 64 (sigWords words) := by bv_omega
    by_cases hone : sigWords words = 1
    · have hpositive : 0 < words.length := by have := sigWords_le_length words; omega
      have hword : read_mem_bytes 8 pointer s = words[0]?.getD 0#64 := by
        simpa using (scan_limb s pointer words 0 hpositive hs hm).2.2
      let ops : List Op := [.p304, .p308, .p312, .p316, .p924]
      let t := block base ops s
      have hf : Follows base ops s := by
        simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
          hpc, h2, hcount, hsum, hadd, hone, BitVec.add_assoc]
      refine ⟨5, t, block_run base ops s hc he ha hf,
        scan_pure_frame base ops s (by decide), ?_, ?_, ?_⟩
      all_goals simp [t, ops, block, Op.effect, put, next, state_simp_rules,
        hpc, h1, h2, hcount, hsum, hadd, hone, hword, BitVec.add_assoc]
    · have hgt : ¬ sigWords words ≤ 1 := by omega
      have hne : BitVec.ofNat 64 (sigWords words) ≠ 1#64 := by bv_omega
      let ops : List Op := [.p304, .p308, .p312, .p316]
      let t := block base ops s
      have hf : Follows base ops s := by
        simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
          hpc, h2, hcount, hsum, hadd, hne, BitVec.add_assoc]
      refine ⟨4, t, block_run base ops s hc he ha hf,
        scan_pure_frame base ops s (by decide), ?_, ?_, ?_⟩
      all_goals simp [t, ops, block, Op.effect, put, next, state_simp_rules,
        hpc, h1, h2, hcount, hsum, hadd, hne, hgt, BitVec.add_assoc]

end SszArm.NatMulWord

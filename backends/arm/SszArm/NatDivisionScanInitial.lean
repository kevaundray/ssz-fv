import SszArm.NatDivisionScan

namespace SszArm.NatDivision

open UintCodec SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Entry and significant-width classification, preserving the original physical
X2 count. The all-zero path deliberately retains the native pc328 dispatch. -/
theorem initial_scan (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 36#64)
    (h1 : r (.GPR 1#5) s = pointer)
    (h2 : r (.GPR 2#5) s = BitVec.ofNat 64 words.length)
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧
      read_pc t = base + BitVec.ofNat 64
        (if sigWords words = 0 then 328 else if sigWords words < 3 then 332 else 104) ∧
      (sigWords words ≠ 0 → r (.GPR 8#5) t = BitVec.ofNat 64 (sigWords words)) := by
  let u := Op.p36.effect base s
  have hu : run 1 s = u := by
    change stepi s = u
    exact step s base .p36 hc hp he ha
  have huf : ScanFrame s u := scan_pure_frame base [.p36] s (by decide)
  have hpc0 : r .PC s = base + 36#64 := hp
  have hup : read_pc u = base + 40#64 := by
    simp [u, Op.effect, put, next, state_simp_rules, hpc0, BitVec.add_assoc]
  have hu1 : r (.GPR 1#5) u = pointer := by
    simpa [u, Op.effect, put, next, state_simp_rules] using h1
  have hu9 : r (.GPR 9#5) u = BitVec.ofNat 64 words.length - 1#64 := by
    simp [u, Op.effect, put, next, state_simp_rules, h2]
  obtain ⟨fuel, v, hv, hvf, hvkeep, hvp, hv8⟩ := significant_scan base pointer words false
    words.length u (Nat.le_refl _) (huf.code hc) (huf.error.trans he) (huf.aligned ha)
    hup hu1 hu9 (huf.source _ _ hs) (huf.words _ _ hs hm)
  have hsf := huf.trans hvf
  by_cases hz : sigWords words = 0
  · refine ⟨1 + fuel, v, ?_, hsf, ?_, ?_⟩
    · rw [run_plus, hu, hv]
    · change read_pc v = base + BitVec.ofNat 64 (scanExit false (sigWords words)) at hvp
      simpa [scanExit, hz] using hvp
    · simp [hz]
  · have hvp' : read_pc v = base + 92#64 := by
      simpa [scanExit, show significantCount words words.length ≠ 0 from hz] using hvp
    have hv8' : r (.GPR 8#5) v = BitVec.ofNat 64 (sigWords words - 1) := hv8 hz
    have hbound : sigWords words < 2^64 := by
      have := hs.2.1
      have := sigWords_le_length words
      omega
    have hcount : BitVec.ofNat 64 (sigWords words - 1) + 1#64 =
        BitVec.ofNat 64 (sigWords words) := by bv_omega
    let ops : List Op := [.p92, .p96, .p100]
    let t := block base ops v
    have hpc : r .PC v = base + 92#64 := hvp'
    have hf : Follows base ops v := by
      simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
        hpc, BitVec.add_assoc]
    have ht : run 3 v = t := block_run base ops v (hsf.code hc)
      (hsf.error.trans he) (hsf.aligned ha) hf
    have hcarry : (AddWithCarry (BitVec.ofNat 64 (sigWords words)) (~~~3#64) 1#1).2.c = 1#1 ↔
        3 ≤ sigWords words := by
      rw [Udivti3.cmp_carry]
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound]
    change (AddWithCarry (BitVec.ofNat 64 (sigWords words)) 18446744073709551612#64 1#1).2.c = 1#1 ↔
      3 ≤ sigWords words at hcarry
    refine ⟨1 + fuel + 3, t, ?_, hsf.trans (scan_pure_frame base ops v (by decide)), ?_, ?_⟩
    · rw [run_plus, run_plus, hu, hv, ht]
    · by_cases hsmall : sigWords words < 3
      · simp [t, ops, block, Op.effect, put, next, state_simp_rules,
          hv8', hcount, hcarry, hz, hsmall, show ¬ 3 ≤ sigWords words by omega]
      · simp [t, ops, block, Op.effect, put, next, state_simp_rules,
          hv8', hcount, hcarry, hz, hsmall, show 3 ≤ sigWords words by omega]
    · intro h
      simp [t, ops, block, Op.effect, put, next, state_simp_rules, hv8', hcount]

end SszArm.NatDivision

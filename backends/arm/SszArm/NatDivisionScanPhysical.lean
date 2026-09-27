import SszArm.NatDivisionScan

namespace SszArm.NatDivision

open UintCodec SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def physicalGuardOps : List Op := [.p120, .p124, .p128]
def physicalTailOps : List Op := [.p160, .p164]

def physicalRoundResult (s : ArmState) (base word : BitVec 64) : ArmState :=
  block base physicalTailOps
    (scanLoadResult (block base physicalGuardOps s) base .physical word)

theorem physical_scan_round (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (n : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 120#64)
    (h9 : r (.GPR 9#5) s = pointer - 8#64)
    (h8 : r (.GPR 8#5) s = BitVec.ofNat 64 (n + 2))
    (h23 : r (.GPR 23#5) s = BitVec.ofNat 64 (8 * (n + 1)))
    (hn : n < words.length) (hs : NatCompare.Source s pointer words)
    (hm : NatCompare.Words s pointer words) :
    let t := physicalRoundResult s base (words[n]?.getD 0#64)
    run 12 s = t ∧ ScanFrame s t ∧
      r (.GPR 9#5) t = pointer - 8#64 ∧
      r (.GPR 8#5) t = BitVec.ofNat 64 (n + 1) ∧
      r (.GPR 22#5) t = BitVec.ofNat 64 (n + 2) ∧
      r (.GPR 23#5) t = BitVec.ofNat 64 (8 * n) ∧
      r (.GPR 24#5) t = r (.GPR 24#5) s ∧
      read_pc t = if words[n]?.getD 0#64 = 0#64 then base + 120#64 else base + 168#64 := by
  have hbound : words.length + 1 < 2^64 := by have := hs.2.1; omega
  have hne : BitVec.ofNat 64 (n + 2) ≠ 1#64 := by bv_omega
  let u := block base physicalGuardOps s
  have hpc : r .PC s = base + 120#64 := hp
  have hfollow : Follows base physicalGuardOps s := by
    simp [physicalGuardOps, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, hpc, BitVec.add_assoc]
  have hu : run 3 s = u := block_run base physicalGuardOps s hc he ha hfollow
  have huf : ScanFrame s u := scan_pure_frame base _ s (by decide)
  have hup : read_pc u = base + 132#64 := by
    simp [u, physicalGuardOps, block, Op.effect, put, next, state_simp_rules, h8, hne]
  have hus := huf.source pointer words hs
  have hum := huf.words pointer words hs hm
  have hload : read_mem_bytes 8 (ScanLoad.physical.address u)
      (NatCompare.saved u 11#5) = words[n]?.getD 0#64 := by
    have hadd : ScanLoad.physical.address u = pointer + (BitVec.ofNat 64 n <<< 3) := by
      simp [u, physicalGuardOps, ScanLoad.address, block, Op.effect, put, next,
        state_simp_rules, h9, h23]
      bv_omega
    rw [hadd]
    exact NatCompare.limb_load u pointer words n 11#5 hn hus hum
  let v := scanLoadResult u base .physical (words[n]?.getD 0#64)
  have hv : run 7 u = v := scan_load_run u base _ .physical
    (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup hus.1 hload
  have hvf := huf.trans (scan_load_frame u base (words[n]?.getD 0#64) .physical hus.1)
  have htail : Follows base physicalTailOps v := by
    simp [v, physicalTailOps, scanLoadResult, ScanLoad.start, ScanLoad.size,
      Follows, Op.row, Op.effect, put, next, state_simp_rules, BitVec.add_assoc]
  have ht : run 2 v = block base physicalTailOps v :=
    block_run base physicalTailOps v (hvf.code hc) (hvf.error.trans he) (hvf.aligned ha) htail
  refine ⟨?_, hvf.trans (scan_pure_frame base _ v (by decide)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 12 = 3 + 7 + 2 by decide, run_plus, run_plus, hu, hv, ht]
    rfl
  all_goals simp [physicalRoundResult, physicalTailOps, physicalGuardOps,
    scanLoadResult, block, Op.effect, put, next, NatCompare.saved, state_simp_rules,
    h9, h8, h23, BitVec.ofNat_add]
  all_goals bv_omega

/-- The second scan repeats the physical traversal. In particular X22 retains
one more than the significant count, not one more than the physical length. -/
theorem physical_scan (base pointer : BitVec 64) (words : List (BitVec 64)) :
    ∀ n (s : ArmState), n ≤ words.length →
      CodeAt s base → read_err s = .None → CheckSPAlignment s →
      read_pc s = base + 120#64 →
      r (.GPR 9#5) s = pointer - 8#64 →
      r (.GPR 8#5) s = BitVec.ofNat 64 (n + 1) →
      r (.GPR 23#5) s = BitVec.ofNat 64 (8 * n) →
      NatCompare.Source s pointer words → NatCompare.Words s pointer words →
      ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧
        r (.GPR 8#5) t = BitVec.ofNat 64 (significantCount words n) ∧
        r (.GPR 22#5) t = BitVec.ofNat 64 (significantCount words n + 1) ∧
        (significantCount words n ≠ 0 →
          r (.GPR 23#5) t = BitVec.ofNat 64 (8 * (significantCount words n - 1))) ∧
        r (.GPR 24#5) t = r (.GPR 24#5) s ∧
        read_pc t = if significantCount words n = 0 then base + 1028#64 else base + 168#64 := by
  intro n
  induction n with
  | zero =>
    intro s hn hc he ha hp h9 h8 h23 hs hm
    let t := block base physicalGuardOps s
    have hpc : r .PC s = base + 120#64 := hp
    have hf : Follows base physicalGuardOps s := by
      simp [physicalGuardOps, Follows, Op.row, Op.effect, put, next,
        state_simp_rules, hpc, BitVec.add_assoc]
    refine ⟨3, t, block_run base physicalGuardOps s hc he ha hf,
      scan_pure_frame base _ s (by decide), ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [t, physicalGuardOps, block, Op.effect, put, next,
      state_simp_rules, h8, significantCount]
  | succ n ih =>
    intro s hn hc he ha hp h9 h8 h23 hs hm
    obtain ⟨hu, huf, hu9, hu8, hu22, hu23, hu24, hup⟩ :=
      physical_scan_round s base pointer words n hc he ha hp h9 h8 h23 (by omega) hs hm
    let u := physicalRoundResult s base (words[n]?.getD 0#64)
    change run 12 s = u at hu
    change ScanFrame s u at huf
    change r (.GPR 9#5) u = pointer - 8#64 at hu9
    change r (.GPR 8#5) u = BitVec.ofNat 64 (n + 1) at hu8
    change r (.GPR 22#5) u = BitVec.ofNat 64 (n + 2) at hu22
    change r (.GPR 23#5) u = BitVec.ofNat 64 (8 * n) at hu23
    change r (.GPR 24#5) u = r (.GPR 24#5) s at hu24
    change read_pc u = if words[n]?.getD 0#64 = 0#64 then base + 120#64 else base + 168#64 at hup
    by_cases hz : words[n]?.getD 0#64 = 0#64
    · obtain ⟨fuel, t, ht, htf, ht8, ht22, ht23, ht24, htp⟩ := ih u (by omega)
        (huf.code hc) (huf.error.trans he) (huf.aligned ha)
        (by simpa [hz] using hup) hu9 hu8 hu23
        (huf.source _ _ hs) (huf.words _ _ hs hm)
      refine ⟨12 + fuel, t, ?_, huf.trans htf, ?_, ?_, ?_, ht24.trans hu24, ?_⟩
      · rw [run_plus, hu, ht]
      · simpa [significantCount, hz] using ht8
      · simpa [significantCount, hz] using ht22
      · simpa [significantCount, hz] using ht23
      · simpa [significantCount, hz] using htp
    · refine ⟨12, u, hu, huf, ?_, ?_, ?_, hu24, ?_⟩
      · simpa [significantCount, hz] using hu8
      · simpa [significantCount, hz] using hu22
      · intro h; simpa [significantCount, hz] using hu23
      · simpa [significantCount, hz] using hup

/-- Entry to the redundant physical scan uses the original X2 length. -/
theorem physical_scan_entry (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 104#64)
    (h1 : r (.GPR 1#5) s = pointer)
    (h2 : r (.GPR 2#5) s = BitVec.ofNat 64 words.length)
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧
      r (.GPR 8#5) t = BitVec.ofNat 64 (significantCount words words.length) ∧
      r (.GPR 22#5) t = BitVec.ofNat 64 (significantCount words words.length + 1) ∧
      (significantCount words words.length ≠ 0 →
        r (.GPR 23#5) t = BitVec.ofNat 64 (8 * (significantCount words words.length - 1))) ∧
      r (.GPR 24#5) t = 8#64 ∧
      read_pc t = if significantCount words words.length = 0 then base + 1028#64 else base + 168#64 := by
  let ops : List Op := [.p104, .p108, .p112, .p116]
  let u := block base ops s
  have hpc : r .PC s = base + 104#64 := hp
  have hf : Follows base ops s := by
    simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]
  have hu : run 4 s = u := block_run base ops s hc he ha hf
  have huf : ScanFrame s u := scan_pure_frame base ops s (by decide)
  have hup : read_pc u = base + 120#64 := by
    simp [u, ops, block, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]
  have hu9 : r (.GPR 9#5) u = pointer - 8#64 := by
    simp [u, ops, block, Op.effect, put, next, state_simp_rules, h1]
  have hu8 : r (.GPR 8#5) u = BitVec.ofNat 64 (words.length + 1) := by
    simp [u, ops, block, Op.effect, put, next, state_simp_rules, h2, BitVec.ofNat_add]
  have hu23 : r (.GPR 23#5) u = BitVec.ofNat 64 (8 * words.length) := by
    simp [u, ops, block, Op.effect, put, next, state_simp_rules, h2]
    bv_omega
  have hu24 : r (.GPR 24#5) u = 8#64 := by
    simp [u, ops, block, Op.effect, put, next, state_simp_rules]
  obtain ⟨fuel, t, ht, htf, ht8, ht22, ht23, ht24, htp⟩ :=
    physical_scan base pointer words words.length u (Nat.le_refl _)
      (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup hu9 hu8 hu23
      (huf.source _ _ hs) (huf.words _ _ hs hm)
  refine ⟨4 + fuel, t, ?_, huf.trans htf, ht8, ht22, ht23, ht24.trans hu24, htp⟩
  rw [run_plus, hu, ht]

end SszArm.NatDivision

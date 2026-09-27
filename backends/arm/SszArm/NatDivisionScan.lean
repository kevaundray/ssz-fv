import SszArm.NatDivisionScanLoad
import SszArm.NatCompareOrder

namespace SszArm.NatDivision

open UintCodec SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def scanHead (quotient : Bool) : Nat := if quotient then 1036 else 40

def scanPointerReg (quotient : Bool) : BitVec 5 := if quotient then 24#5 else 1#5

def scanLoadKind (quotient : Bool) : ScanLoad := if quotient then .quotient else .initial

def scanGuardOps (quotient : Bool) : List Op :=
  if quotient then [.p1036, .p1040] else [.p40, .p44]

def scanTailOps (quotient : Bool) : List Op :=
  if quotient then [.p1076, .p1080, .p1084] else [.p80, .p84, .p88]

def scanExit (quotient : Bool) (count : Nat) : Nat :=
  if count = 0 then (if quotient then 1108 else 328)
  else (if quotient then 1088 else 92)

def scanRoundResult (s : ArmState) (base word : BitVec 64) (quotient : Bool) : ArmState :=
  block base (scanTailOps quotient)
    (scanLoadResult (block base (scanGuardOps quotient) s) base (scanLoadKind quotient) word)

theorem significant_scan_round (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (n : Nat) (quotient : Bool)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 (scanHead quotient))
    (hptr : r (.GPR (scanPointerReg quotient)) s = pointer)
    (hn : n < words.length) (h9 : r (.GPR 9#5) s = BitVec.ofNat 64 n)
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    let t := scanRoundResult s base (words[n]?.getD 0#64) quotient
    run 13 s = t ∧ ScanFrame s t ∧
      (∀ reg ∈ [22#5, 23#5, 24#5], r (.GPR reg) t = r (.GPR reg) s) ∧
      r (.GPR 9#5) t = BitVec.ofNat 64 n - 1#64 ∧
      r (.GPR 8#5) t = BitVec.ofNat 64 n ∧
      read_pc t = base + BitVec.ofNat 64
        (if words[n]?.getD 0#64 = 0#64 then scanHead quotient
         else if quotient then 1088 else 92) := by
  have hbound : words.length < 2^64 := by have := hs.2.1; omega
  have hnonzero : BitVec.ofNat 64 n + 1#64 ≠ 0#64 := by bv_omega
  let u := block base (scanGuardOps quotient) s
  have hpc : r .PC s = base + BitVec.ofNat 64 (scanHead quotient) := hp
  have hfollow : Follows base (scanGuardOps quotient) s := by
    cases quotient <;> simp [scanGuardOps, scanHead, Follows, Op.row,
      Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]
  have hu : run 2 s = u := by
    have hrun := block_run base (scanGuardOps quotient) s hc he ha hfollow
    cases quotient <;> simpa [u, scanGuardOps] using hrun
  have huf : ScanFrame s u := scan_pure_frame base _ s (by cases quotient <;> decide)
  have hup : read_pc u = base + BitVec.ofNat 64 (scanLoadKind quotient).start := by
    cases quotient <;> simp [u, scanGuardOps, scanLoadKind, ScanLoad.start,
      block, Op.effect, put, next, state_simp_rules, h9, hnonzero]
  have hu9 : r (.GPR 9#5) u = BitVec.ofNat 64 n := by
    cases quotient <;> simpa [u, scanGuardOps, block, Op.effect, put, next,
      state_simp_rules] using h9
  have huptr : r (.GPR (scanPointerReg quotient)) u = pointer := by
    cases quotient <;> simpa [u, scanGuardOps, scanPointerReg, block, Op.effect,
      put, next, state_simp_rules] using hptr
  have hus := huf.source pointer words hs
  have hum := huf.words pointer words hs hm
  have hload : read_mem_bytes 8 ((scanLoadKind quotient).address u)
      (NatCompare.saved u 11#5) = words[n]?.getD 0#64 := by
    have hadd : (scanLoadKind quotient).address u = pointer + (BitVec.ofNat 64 n <<< 3) := by
      cases quotient <;> simpa [scanLoadKind, ScanLoad.address, scanPointerReg, hu9] using
        congrArg (fun p => p + (BitVec.ofNat 64 n <<< 3)) huptr
    rw [hadd]
    exact NatCompare.limb_load u pointer words n 11#5 hn hus hum
  let v := scanLoadResult u base (scanLoadKind quotient) (words[n]?.getD 0#64)
  have hv : run 8 u = v := by
    have hrun := scan_load_run u base _
      (scanLoadKind quotient) (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup hus.1 hload
    cases quotient <;> simpa [v, scanLoadKind, ScanLoad.size] using hrun
  have hvf : ScanFrame s v := huf.trans (scan_load_frame u base _ _ hus.1)
  have htail : Follows base (scanTailOps quotient) v := by
    cases quotient <;> simp [v, scanLoadKind, scanTailOps, ScanLoad.start,
      ScanLoad.size, scanLoadResult, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, BitVec.add_assoc]
  have ht : run 3 v = block base (scanTailOps quotient) v := by
    have hrun := block_run base (scanTailOps quotient) v
      (hvf.code hc) (hvf.error.trans he) (hvf.aligned ha) htail
    cases quotient <;> simpa [scanTailOps] using hrun
  refine ⟨?_, hvf.trans (scan_pure_frame base _ v (by cases quotient <;> decide)), ?_, ?_, ?_, ?_⟩
  · rw [show 13 = 2 + 8 + 3 by decide, run_plus, run_plus, hu, hv, ht]
    rfl
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> cases quotient <;>
      simp [scanRoundResult, scanTailOps, scanLoadKind, scanLoadResult,
        scanGuardOps, block, Op.effect, put, next, NatCompare.saved, state_simp_rules]
  all_goals cases quotient <;>
    simp [scanRoundResult, scanTailOps, scanLoadKind, scanLoadResult,
      scanGuardOps, scanHead, block, Op.effect, put, next, NatCompare.saved,
      state_simp_rules, h9, apply_ite]

/-- Complete native descending scan, including the all-zero and empty cases.
No canonicality is assumed: the physical list can contain any high zero suffix. -/
theorem significant_scan (base pointer : BitVec 64) (words : List (BitVec 64))
    (quotient : Bool) :
    ∀ n (s : ArmState), n ≤ words.length →
      CodeAt s base → read_err s = .None → CheckSPAlignment s →
      read_pc s = base + BitVec.ofNat 64 (scanHead quotient) →
      r (.GPR (scanPointerReg quotient)) s = pointer →
      r (.GPR 9#5) s = BitVec.ofNat 64 n - 1#64 →
      NatCompare.Source s pointer words → NatCompare.Words s pointer words →
      ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧
        (∀ reg ∈ [22#5, 23#5, 24#5], r (.GPR reg) t = r (.GPR reg) s) ∧
        read_pc t = base + BitVec.ofNat 64 (scanExit quotient (significantCount words n)) ∧
        (significantCount words n ≠ 0 →
          r (.GPR 8#5) t = BitVec.ofNat 64 (significantCount words n - 1)) := by
  intro n
  induction n with
  | zero =>
    intro s hn hc he ha hp hptr h9 hs hm
    let t := block base (scanGuardOps quotient) s
    have hpc : r .PC s = base + BitVec.ofNat 64 (scanHead quotient) := hp
    have hf : Follows base (scanGuardOps quotient) s := by
      cases quotient <;> simp [scanGuardOps, scanHead, Follows, Op.row,
        Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]
    refine ⟨2, t, ?_, scan_pure_frame base _ s (by cases quotient <;> decide), ?_, ?_, ?_⟩
    · have hrun := block_run base (scanGuardOps quotient) s hc he ha hf
      cases quotient <;> simpa [t, scanGuardOps] using hrun
    · intro reg hr
      cases quotient <;> simp [t, scanGuardOps, block, Op.effect, put, next, state_simp_rules]
    · cases quotient <;> simp [t, scanGuardOps, scanExit, significantCount,
        block, Op.effect, put, next, state_simp_rules, h9]
    · simp [significantCount]
  | succ n ih =>
    intro s hn hc he ha hp hptr h9 hs hm
    have h9' : r (.GPR 9#5) s = BitVec.ofNat 64 n := by
      simpa [BitVec.ofNat_add, BitVec.add_sub_cancel] using h9
    obtain ⟨hu, huf, hkeep, hu9, hu8, hup⟩ :=
      significant_scan_round s base pointer words n quotient hc he ha hp hptr (by omega) h9' hs hm
    let u := scanRoundResult s base (words[n]?.getD 0#64) quotient
    change run 13 s = u at hu
    change ScanFrame s u at huf
    change (∀ reg ∈ [22#5, 23#5, 24#5], r (.GPR reg) u = r (.GPR reg) s) at hkeep
    change r (.GPR 9#5) u = BitVec.ofNat 64 n - 1#64 at hu9
    change r (.GPR 8#5) u = BitVec.ofNat 64 n at hu8
    change read_pc u = base + BitVec.ofNat 64
      (if words[n]?.getD 0#64 = 0#64 then scanHead quotient else if quotient then 1088 else 92) at hup
    by_cases hz : words[n]?.getD 0#64 = 0#64
    · have hupp : r (.GPR (scanPointerReg quotient)) u = pointer := by
        cases quotient with
        | false => exact (huf.registers 1#5 (by decide)).trans hptr
        | true => exact (hkeep 24#5 (by decide)).trans hptr
      obtain ⟨fuel, t, ht, htf, htk, htp, ht8⟩ := ih u (by omega)
        (huf.code hc) (huf.error.trans he) (huf.aligned ha)
        (by simpa [hz] using hup) hupp hu9 (huf.source _ _ hs) (huf.words _ _ hs hm)
      refine ⟨13 + fuel, t, ?_, huf.trans htf,
        fun reg hr => (htk reg hr).trans (hkeep reg hr), ?_, ?_⟩
      · rw [run_plus, hu, ht]
      · simpa [significantCount, hz] using htp
      · simpa [significantCount, hz] using ht8
    · refine ⟨13, u, hu, huf, hkeep, ?_, ?_⟩
      · simpa [scanExit, significantCount, hz] using hup
      · intro h
        simpa [significantCount, hz] using hu8

end SszArm.NatDivision

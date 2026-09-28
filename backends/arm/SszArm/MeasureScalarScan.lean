import SszArm.MeasureScalarScanRound

namespace SszArm.Measure.Scalar.Bytes

open SszNative.Limbs

/-- The inlined byte-cap loop scans the physically stored limb list, including
empty lists and an unbounded redundant high-zero suffix. -/
theorem significant_scan (kind : Kind) (base pointer : BitVec 64) (words : List (BitVec 64)) :
    ∀ n (s : ArmState), n ≤ words.length → CodeAt s base → read_err s = .None →
      CheckSPAlignment s → read_pc s = base + BitVec.ofNat 64 kind.scanGuard →
      r (.GPR 8#5) s = pointer →
      r (.GPR 11#5) s = BitVec.ofNat 64 n - 1#64 →
      NatCompare.Source s pointer words → NatCompare.Words s pointer words →
      ∃ fuel t, run fuel s = t ∧ NatNarrow.Frame s t ∧
        (∀ reg ∈ kind.scanKept, r (.GPR reg) t = r (.GPR reg) s) ∧
        read_pc t = base + BitVec.ofNat 64
          (if significantCount words n = 0 then kind.scanZero else kind.scanExit) ∧
        (significantCount words n ≠ 0 →
          kind.remembered t = BitVec.ofNat 64 (significantCount words n - 1)) := by
  intro n
  induction n with
  | zero =>
    intro s within code error aligned pc ptr index source stored
    let t := scanGuardResult kind s base
    refine ⟨2, t, scan_guard_run kind s base code error pc,
      scan_guard_frame kind s base, ?_, ?_, ?_⟩
    · intro reg member
      exact scan_guard_register kind s base reg
    · simp [t, scanGuardResult, significantCount, state_simp_rules, index]
    · simp [significantCount]
  | succ n induction =>
    intro s within code error aligned pc ptr index source stored
    have index' : r (.GPR 11#5) s = BitVec.ofNat 64 n := by
      simpa [BitVec.ofNat_add, BitVec.add_sub_cancel] using index
    obtain ⟨hu, uf, kept, ui, remembered, up⟩ :=
      scan_round kind s base pointer words n code error aligned pc ptr (by omega)
        index' source stored
    let u := scanRoundResult kind s base (words[n]?.getD 0#64)
    change run (10 + kind.tailOps.length) s = u at hu
    change NatNarrow.Frame s u at uf
    change (∀ reg ∈ kind.scanKept, r (.GPR reg) u = r (.GPR reg) s) at kept
    change r (.GPR 11#5) u = BitVec.ofNat 64 n - 1#64 at ui
    change kind.remembered u = BitVec.ofNat 64 n at remembered
    change read_pc u = base + BitVec.ofNat 64
      (if words[n]?.getD 0#64 = 0#64 then kind.scanGuard else kind.scanExit) at up
    by_cases zero : words[n]?.getD 0#64 = 0#64
    · have upp : r (.GPR 8#5) u = pointer :=
        (kept 8#5 (by cases kind <;> decide)).trans ptr
      obtain ⟨fuel, t, ht, tf, tk, tp, tr⟩ := induction u (by omega)
        (code.congr uf.program) (uf.error.trans error) (uf.aligned aligned)
        (by simpa [zero] using up) upp ui (uf.source _ _ source) (uf.words _ _ source stored)
      refine ⟨10 + kind.tailOps.length + fuel, t, ?_, uf.trans tf,
        fun reg member => (tk reg member).trans (kept reg member), ?_, ?_⟩
      · rw [run_plus, hu, ht]
      · simpa [significantCount, zero] using tp
      · simpa [significantCount, zero] using tr
    · refine ⟨10 + kind.tailOps.length, u, hu, uf, kept, ?_, ?_⟩
      · simpa [significantCount, zero] using up
      · intro positive
        simpa [significantCount, zero] using remembered

end SszArm.Measure.Scalar.Bytes

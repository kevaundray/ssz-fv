import SszArm.MeasureBitVectorScanRound

namespace SszArm.Measure.BitVector

open SszNative.Limbs

/-- Every stored high zero is scanned. In particular, empty Large operands and
noncanonical all-zero operands reach the real zero-width branch. -/
theorem significant_scan (base pointer : BitVec 64) (words : List (BitVec 64)) :
    ∀ n (s : ArmState), n ≤ words.length → CodeAt s base → read_err s = .None →
      CheckSPAlignment s → read_pc s = base + 592#64 →
      r (.GPR 11#5) s = pointer → r (.GPR 13#5) s = BitVec.ofNat 64 n - 1#64 →
      NatCompare.Source s pointer words → NatCompare.Words s pointer words →
      ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧ r (.GPR 9#5) t = r (.GPR 9#5) s ∧
        read_pc t = base + BitVec.ofNat 64
          (if significantCount words n = 0 then 2828 else 644) ∧
        (significantCount words n ≠ 0 →
          r (.GPR 12#5) t = BitVec.ofNat 64 (significantCount words n - 1)) := by
  intro n
  induction n with
  | zero =>
    intro s within code error aligned pc ptr index source stored
    let t := scanGuardResult s base
    refine ⟨2, t, scan_guard_run s base code error pc,
      scan_guard_frame s base, scan_guard_register s base 9#5, ?_, ?_⟩
    · simp [t, scanGuardResult, significantCount, state_simp_rules, index]
    · simp [significantCount]
  | succ n induction =>
    intro s within code error aligned pc ptr index source stored
    have index' : r (.GPR 13#5) s = BitVec.ofNat 64 n := by
      simpa [BitVec.ofNat_add, BitVec.add_sub_cancel] using index
    obtain ⟨hu, uf, high, ui, remembered, up⟩ :=
      scan_round s base pointer words n code error aligned pc ptr (by omega)
        index' source stored
    let u := scanRoundResult s base (words[n]?.getD 0#64)
    change run 13 s = u at hu
    change ScanFrame s u at uf
    change r (.GPR 9#5) u = r (.GPR 9#5) s at high
    change r (.GPR 13#5) u = BitVec.ofNat 64 n - 1#64 at ui
    change r (.GPR 12#5) u = BitVec.ofNat 64 n at remembered
    change read_pc u = base + BitVec.ofNat 64
      (if words[n]?.getD 0#64 = 0#64 then 592 else 644) at up
    by_cases zero : words[n]?.getD 0#64 = 0#64
    · have upp : r (.GPR 11#5) u = pointer :=
        (uf.registers 11#5 (by decide)).trans ptr
      obtain ⟨fuel, t, ht, tf, th, tp, tr⟩ := induction u (by omega)
        (code.congr uf.program) (uf.error.trans error) (uf.aligned aligned)
        (by simpa [zero] using up) upp ui (uf.source _ _ source) (uf.words _ _ source stored)
      refine ⟨13 + fuel, t, ?_, uf.trans tf, th.trans high, ?_, ?_⟩
      · rw [run_plus, hu, ht]
      · simpa [significantCount, zero] using tp
      · simpa [significantCount, zero] using tr
    · refine ⟨13, u, hu, uf, high, ?_, ?_⟩
      · simpa [significantCount, zero] using up
      · intro positive
        simpa [significantCount, zero] using remembered

end SszArm.Measure.BitVector

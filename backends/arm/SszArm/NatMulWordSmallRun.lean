import SszArm.NatMulWordSmallDispatch
import SszArm.NatMulWordWideRun

namespace SszArm.NatMulWord

/-- Complete significant-at-most-one-word execution from the real PC928.
The current scan checkpoint is physical state, not an assumed future outcome. -/
theorem small_checkpoint_run (s u : ArmState) (base factor : BitVec 64)
    (operand : SszNative.NatOperand) (owned : Owned s operand factor)
    (priorFrame : SmallFrame s u) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc u = base + 928#64)
    (low : r (.GPR 2#5) u = SszNative.NatMul.lowWord operand)
    (nonzero : factor ≠ 0#64) (notone : factor ≠ 1#64) (small : operand.wordCount ≤ 1) :
    ∃ fuel t, run fuel u = t ∧ Post s t operand factor := by
  let a := highCompleted .small u base
  have stack : 48 ≤ (r (.GPR 31#5) u).toNat := by
    simpa only [priorFrame.sp] using owned.stackBound
  have ar := high_run .small u base (priorFrame.code code) (priorFrame.error.trans error)
    (priorFrame.aligned aligned) pc
  have af : SmallFrame s a := priorFrame.trans (small_high_frame u base stack)
  have ap : read_pc a = base + 1040#64 := by
    rw [high_completed_pc, pc]
    simp [BitVec.add_assoc]
  have factorReg : r (.GPR 3#5) u = factor :=
    (priorFrame.registers _ (by decide)).trans owned.factorRegister
  have ah : r (.GPR 9#5) a = NatMulProduct.high (SszNative.NatMul.lowWord operand) factor := by
    simpa only [HighSite.destination, HighSite.left, low, factorReg] using
      high_completed_value .small u base
  have al : r (.GPR 2#5) a = SszNative.NatMul.lowWord operand :=
    (high_completed_registers .small u base stack 2#5 (by decide)).trans low
  have ak : r (.GPR 3#5) a = factor :=
    (high_completed_registers .small u base stack 3#5 (by decide)).trans factorReg
  let b := smallDispatch a base
  have br := small_dispatch_run a base (af.code code) (af.error.trans error) (af.aligned aligned) ap
  have bf : SmallFrame s b := af.trans (small_dispatch_frame a base)
  have bp := small_dispatch_pc a base ap
  have bl : r (.GPR 8#5) b = SszNative.NatMul.lowWord operand * factor := by
    rw [small_dispatch_low, al, ak]
  have bh : r (.GPR 9#5) b = NatMulProduct.high (SszNative.NatMul.lowWord operand) factor :=
    (small_dispatch_high a base).trans ah
  by_cases narrow : NatMulProduct.high (SszNative.NatMul.lowWord operand) factor = 0#64
  · have exit : read_pc b = base + 1048#64 := by
      simpa only [ah, narrow, ↓reduceIte] using bp
    have model : outcome s operand factor = SszNative.NatArithmetic.unchanged (arenaOf s).used
        (.ok (.small (SszNative.NatMul.lowWord operand * factor))) :=
      small_narrow_model operand factor _ _ _ nonzero notone small narrow
    have finish := small_narrow_finish s b base factor (SszNative.NatMul.lowWord operand * factor)
      operand owned bf code error aligned exit bl model
    refine ⟨28 + (2 + 21), valueResult .small base b, ?_, finish.2⟩
    rw [run_plus, ar, run_plus, br, finish.1]
  · have exit : read_pc b = base + 1132#64 := by
      simpa only [ah, narrow, ↓reduceIte] using bp
    have product : SszNative.NatMul.wordProduct operand factor = r (.GPR 9#5) b ++ r (.GPR 8#5) b := by
      rw [bh, bl]
      exact small_word_product operand factor
    obtain ⟨fuel, t, tr, post⟩ := wide_run_from_current s b base factor operand owned bf
      code error aligned exit nonzero notone small product (by rw [bh]; exact narrow)
    refine ⟨28 + (2 + fuel), t, ?_, post⟩
    rw [run_plus, ar, run_plus, br, tr]

/-- Original entry through original RET for the entire small-significant branch,
including padded Large inputs, narrow success, wide success and reservation error. -/
theorem small_run (s : ArmState) (base : BitVec 64) (operand : SszNative.NatOperand)
    (factor : BitVec 64) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (owned : Owned s operand factor)
    (pc : read_pc s = base + BitVec.ofNat 64 entry)
    (nonzero : factor ≠ 0#64) (notone : factor ≠ 1#64) (small : operand.wordCount ≤ 1) :
    ∃ fuel t, run fuel s = t ∧ Post s t operand factor := by
  obtain ⟨scanFuel, u, ur, scan, _, ready⟩ := general_ready s base factor operand code error aligned
    (by simpa only [entry, BitVec.add_zero] using pc) owned nonzero notone
  simp only [GeneralReady, small, ↓reduceIte] at ready
  obtain ⟨fuel, t, tr, post⟩ := small_checkpoint_run s u base factor operand owned
    (scan.small owned.stackBound) code error aligned ready.1 ready.2 nonzero notone small
  exact ⟨scanFuel + fuel, t, by rw [run_plus, ur, tr], post⟩

end SszArm.NatMulWord

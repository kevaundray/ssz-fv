import SszArm.BitVectorFrontier
import SszArm.BitVectorScopeSuccess
import SszArm.BitVectorScopeFailure
import SszArm.BitVectorFinish

namespace SszArm.BitVector

/-- From the physically retained ceiling pair, both scope outcomes, both
padding outcomes, every original-length representation, and the final native
Bits guard are covered by actual instruction execution. -/
theorem expected_executes {s c : ArmState} {base : BitVec 64}
    {length expected : SszNative.NatOperand} {remainder : BitVec 64} {data : Ssz.Bytes}
    (owned : Owned s length data) (aligned : CheckSPAlignment s)
    (current : ExpectedAt s c base length expected remainder data) :
    ∃ fuel t, run fuel c = t ∧ Completed s t base length data := by
  obtain ⟨scopeFuel, checked, scopeRun, scopePost, checkedCurrent, checkedCode, checkedPC, scopeFrame⟩ :=
    scope_executes base owned current.current current.pair current.limbs current.code aligned current.pc
  have checkedResources := current.resources.after_local owned scopeFrame
  have checkedFrame := current.frame.trans ((local_covered s (outcome s length data)).frame scopeFrame)
  cases scope : SszNative.NatNarrow.runExact expected (BitVec.ofNat 64 data.size) with
  | false =>
    obtain ⟨failureFuel, final, failureRun, terminal, failureFrame⟩ :=
      scope_failure_executes base owned current.current.toWorking scopePost scope current.limbs
        checkedCode aligned checkedPC
    have whole : run (scopeFuel + failureFuel) c = final := by
      rw [run_plus, scopeRun, failureRun]
    refine ⟨scopeFuel + failureFuel, final, whole, ?_⟩
    refine ⟨?_, checkedResources.after_local owned failureFrame,
      checkedFrame.trans ((local_covered s (outcome s length data)).frame failureFrame), ?_⟩
    · rw [current.model]
      simpa only [SszNative.BitVector.finish, scope, Bool.false_eq_true, ↓reduceIte] using terminal
    · rw [← failureRun]
      exact checkedCode.run _
  | true =>
    have accepted := scope_success_branch base owned current.current.toWorking checkedCurrent scopePost
      scope checkedCode aligned checkedPC
    let tested := ExpectedStage.Stage.scope.result checked base
    have testedCurrent := checkedCurrent.after_expected .scope base
    have testedFrame := expected_frame owned checkedCurrent.toWorking .scope base
    have testedCode : JointCodeAt tested base := by
      rw [show tested = run 2 checked from accepted.1.symm]
      exact checkedCode.run 2
    have beforeFinish := checkedFrame.trans ((local_covered s (outcome s length data)).frame testedFrame)
    obtain ⟨finishFuel, final, finishRun, terminal, finishFrame⟩ :=
      finish_executes base owned testedCurrent current.arithmetic scope beforeFinish testedCode
        aligned accepted.2
    have whole : run (scopeFuel + 2 + finishFuel) c = final := by
      rw [run_plus, run_plus, scopeRun, accepted.1, finishRun]
    refine ⟨scopeFuel + 2 + finishFuel, final, whole, ?_⟩
    refine ⟨?_, (checkedResources.after_local owned testedFrame).after_local owned finishFrame,
      beforeFinish.trans ((local_covered s (outcome s length data)).frame finishFrame), ?_⟩
    · simpa only [current.model] using terminal
    · rw [← finishRun]
      exact testedCode.run _

end SszArm.BitVector

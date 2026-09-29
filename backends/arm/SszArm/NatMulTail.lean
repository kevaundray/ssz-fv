import SszArm.NatMulEntry
import SszArm.NatMulTailExec

namespace SszArm.NatMul

/-- The right-one branch wins when both counts are one. Argument preparation,
callee-save restoration, and the original tail B are all executed. -/
theorem word_branch_run (s : ArmState) (base : BitVec 64)
    (left right : SszNative.NatOperand) (owned : Owned s left right)
    (code : JointCodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 entry)
    (leftNonzero : left.wordCount ≠ 0) (rightNonzero : right.wordCount ≠ 0)
    (one : right.wordCount = 1 ∨ left.wordCount = 1) :
    ∃ fuel t, run fuel s = t ∧ Post s t left right := by
  obtain ⟨entryFuel, u, entered, frame, exit, _, _⟩ :=
    entry_dispatch s base left right owned code.body error aligned pc
  have notZero : ¬(SszNative.Limbs.sigWords left.words = 0 ∨
      SszNative.Limbs.sigWords right.words = 0) := by
    rintro (zero | zero)
    · exact leftNonzero zero
    · exact rightNonzero zero
  simp only [DispatchExit, notZero, ↓reduceIte] at exit
  by_cases rightOne : right.wordCount = 1
  · have count : SszNative.Limbs.sigWords right.words = 1 := rightOne
    simp only [count, ↓reduceIte] at exit
    obtain ⟨upc, u1, u2, _, u4⟩ := exit
    obtain ⟨prepared, prepareFrame, vpc, v1, v2, v3⟩ := right_one_prepare u base
      (frame.code code.body) (frame.error.trans error) (frame.aligned aligned) upc
    let v := block base [.p228] u
    have currentFrame : EntryFrame s v := frame.dispatch owned.stackBound prepareFrame
    have factor : r (.GPR 3#5) v = SszNative.NatMul.lowWord right := by
      have value : r (.GPR 3#5) v = _ := v3.trans u4
      simp only [SszNative.NatMul.lowWord, SszNative.NatAdd.lowWord]
      arm_word_nf at value ⊢
      exact value
    have model : outcome s left right = SszNative.NatMul.runWord left (SszNative.NatMul.lowWord right)
        (arenaOf s).base (arenaOf s).capacity (arenaOf s).used :=
      SszNative.NatMul.run_right_one left right _ _ _ leftNonzero rightOne
    obtain ⟨fuel, t, execution, post⟩ := tail_checkpoint_run s v base left right left
      (SszNative.NatMul.lowWord right) owned currentFrame code error aligned vpc
      (v1.trans (u1.trans owned.leftPointer)) (v2.trans (u2.trans owned.leftPayload))
      factor owned.leftAt owned.leftOwned model
    refine ⟨entryFuel + (1 + fuel), t, ?_, post⟩
    rw [run_plus, entered, run_plus, prepared, execution]
  · have leftOne : left.wordCount = 1 := one.resolve_left rightOne
    have notRight : SszNative.Limbs.sigWords right.words ≠ 1 := rightOne
    have count : SszNative.Limbs.sigWords left.words = 1 := leftOne
    simp only [notRight, count, ↓reduceIte] at exit
    obtain ⟨upc, u1, u2, u3⟩ := exit
    have factor : r (.GPR 3#5) u = SszNative.NatMul.lowWord left := by
      have value := u3
      simp only [SszNative.NatMul.lowWord, SszNative.NatAdd.lowWord]
      arm_word_nf at value ⊢
      exact value
    have model : outcome s left right = SszNative.NatMul.runWord right (SszNative.NatMul.lowWord left)
        (arenaOf s).base (arenaOf s).capacity (arenaOf s).used :=
      SszNative.NatMul.run_left_one left right _ _ _ leftOne rightNonzero rightOne
    obtain ⟨fuel, t, execution, post⟩ := tail_checkpoint_run s u base left right right
      (SszNative.NatMul.lowWord left) owned frame code error aligned upc
      (u1.trans owned.rightPointer) (u2.trans owned.rightPayload) factor
      owned.rightAt owned.rightOwned model
    exact ⟨entryFuel + fuel, t, by rw [run_plus, entered, execution], post⟩

end SszArm.NatMul

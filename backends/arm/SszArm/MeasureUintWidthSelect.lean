import SszArm.MeasureUintWidthLarge
import SszArm.MeasureUintOwned
import SszArm.MeasureUintCountMath
import SszSerializeMeasure

namespace SszArm.Measure.Uint

open SszNative (NatOperand)
open SszNative.Limbs

/-- Actual width classification and unsigned comparison implement uintFits for
unrestricted logical widths, while retaining the original X21/X20 Nat pair. -/
theorem width_select (s : ArmState) (args : Args) (uintCap number : NatOperand)
    (base : BitVec 64) (owned : Owned s args (.uint uintCap) (.uint number))
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 2740#64) (stack : r (.GPR 31#5) s = args.bodySP)
    (pointerReg : r (.GPR 21#5) s = uintCap.pointer)
    (payloadReg : r (.GPR 20#5) s = uintCap.payload)
    (required : pairValue (r (.GPR 8#5) s) (r (.GPR 9#5) s) =
      SszNative.Serialize.requiredBytes number.value) :
    ∃ fuel t, run fuel s = t ∧ NatNarrow.Frame s t ∧
      read_pc t = if SszNative.Serialize.uintFits uintCap number
        then base + 4144#64 else base + 3924#64 := by
  have pc' : r .PC s = base + 2740#64 := pc
  cases uintCap with
  | small limbWord =>
    let ops : List WidthOp := [.p2740, .p2816, .p2820, .p2824]
    let u := widthBlock base ops s
    have follows : WidthFollows base ops s := by
      simp [ops, WidthFollows, WidthOp.row, WidthOp.effect, put, next,
        Emit.Dispatch.next, state_simp_rules, pc', pointerReg, NatOperand.pointer, BitVec.add_assoc]
    have executed : run 4 s = u := width_run base ops s code error aligned follows
    have frame : NatNarrow.Frame s u := width_pure_frame base _ s (by decide)
    have nextPC : read_pc u = base + 3912#64 := by
      simp [u, ops, widthBlock, WidthOp.effect, put, next, Emit.Dispatch.next, state_simp_rules]
    obtain ⟨compareRun, compareFrame, _, comparePC⟩ := final_compare u base
      (code.congr frame.program) (frame.error.trans error) (frame.aligned aligned) nextPC
    let t := widthBlock base finalCompareOps u
    refine ⟨7, t, ?_, frame.trans compareFrame, ?_⟩
    · rw [show 7 = 4 + 3 by decide, run_plus, executed, compareRun]
    · have inputValue : pairValue (r (.GPR 8#5) u) (r (.GPR 9#5) u) =
          SszNative.Serialize.requiredBytes number.value := by
        simpa [u, ops, widthBlock, WidthOp.effect, put, next,
          Emit.Dispatch.next, state_simp_rules] using required
      have widthValue : pairValue (r (.GPR 10#5) u) (r (.GPR 11#5) u) = limbWord.toNat := by
        simp [u, ops, widthBlock, WidthOp.effect, put, next, Emit.Dispatch.next,
          state_simp_rules, payloadReg, NatOperand.payload, pairValue]
      simpa [inputValue, widthValue, SszNative.Serialize.uintFits,
        NatOperand.value, NatOperand.words, SszNative.Limbs.value] using comparePC
  | large pointer words =>
    have input := owned.operand_at (.large pointer words)
      (by simp [Emit.descriptorOperands, Emit.valueOperands])
    have nonnull : pointer ≠ 0#64 := by
      intro zero
      have positive := input.1
      simp [zero] at positive
    have source := operand_source owned stack pointer words (by simp)
    have memory := operand_words owned pointer words (by simp)
    let ops : List WidthOp := [.p2740, .p2744]
    let u := widthBlock base ops s
    have follows : WidthFollows base ops s := by
      simp [ops, WidthFollows, WidthOp.row, WidthOp.effect,
        state_simp_rules, pc', pointerReg, NatOperand.pointer, nonnull]
    have executed : run 2 s = u := width_run base ops s code error aligned follows
    have frame : NatNarrow.Frame s u := width_pure_frame base _ s (by decide)
    have nextPC : read_pc u = base + 2748#64 := by
      simp [u, ops, widthBlock, WidthOp.effect, put, next, Emit.Dispatch.next,
        state_simp_rules, pointerReg, NatOperand.pointer, nonnull, BitVec.add_assoc]
    have nextPointer : r (.GPR 21#5) u = pointer := by
      simpa [NatOperand.pointer] using (frame.registers 21#5 (by decide)).trans pointerReg
    have nextCount : r (.GPR 20#5) u = BitVec.ofNat 64 words.length := by
      simpa [NatOperand.payload] using (frame.registers 20#5 (by decide)).trans payloadReg
    have nextIndex : r (.GPR 11#5) u = BitVec.ofNat 64 words.length - 1#64 := by
      simp [u, ops, widthBlock, WidthOp.effect, put, next, Emit.Dispatch.next,
        state_simp_rules, payloadReg, NatOperand.payload]
    obtain ⟨extra, v, readyRun, readyFrame, readyPC, readyValue, readyLow, readyHigh⟩ :=
      width_large_ready u base pointer words (code.congr frame.program)
        (frame.error.trans error) (frame.aligned aligned) nextPC nextPointer nextCount nextIndex
        (frame.source _ _ source) (frame.words _ _ source memory)
    have fullFrame := frame.trans readyFrame
    have fullRun : run (2 + extra) s = v := by rw [run_plus, executed, readyRun]
    have inputValue : pairValue (r (.GPR 8#5) v) (r (.GPR 9#5) v) =
        SszNative.Serialize.requiredBytes number.value := by
      rw [readyLow, readyHigh]
      simpa [u, ops, widthBlock, WidthOp.effect, put, next,
        Emit.Dispatch.next, state_simp_rules] using required
    by_cases wide : 2 < sigWords words
    · have large := SszNative.Serialize.wide_width_bound words wide
      have inputBound : SszNative.Serialize.requiredBytes number.value < 2^128 := by
        rw [← required, pairValue_join]
        exact Udivti3.join_lt _ _
      have fits : SszNative.Serialize.uintFits (.large pointer words) number := by
        change SszNative.Serialize.requiredBytes number.value ≤ SszNative.Limbs.value words
        exact Nat.le_trans (Nat.le_of_lt inputBound) large
      refine ⟨2 + extra, v, fullRun, fullFrame, ?_⟩
      simpa [wide, fits] using readyPC
    · have narrow : sigWords words ≤ 2 := by omega
      have compareEntry : read_pc v = base + 3912#64 := by simpa [wide] using readyPC
      obtain ⟨compareRun, compareFrame, _, comparePC⟩ := final_compare v base
        (code.congr fullFrame.program) (fullFrame.error.trans error)
        (fullFrame.aligned aligned) compareEntry
      let t := widthBlock base finalCompareOps v
      refine ⟨2 + extra + 3, t, ?_, fullFrame.trans compareFrame, ?_⟩
      · rw [run_plus, fullRun, compareRun]
      · simp only [t, inputValue, readyValue narrow, SszNative.Serialize.uintFits,
          NatOperand.value, NatOperand.words] at comparePC ⊢
        with_unfolding_all exact comparePC

end SszArm.Measure.Uint

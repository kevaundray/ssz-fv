import SszArm.NatMulWordLargeEntry
import SszArm.NatMulWordLoop

namespace SszArm.NatMulWord.Large

open Delimited (Protected MemoryFrame Returned)
open UintCodec (widthLoad)

theorem loop_return_owned {s t : ArmState} (stable : LoopStable s t)
    (owned : ReturnOwned s) : ReturnOwned t := by
  have out := stable.registers 0#5 (by decide)
  exact ⟨by simpa only [stable.sp] using owned.stack,
    by simpa only [out] using owned.output,
    by simpa only [stable.sp, out] using owned.separate⟩

theorem loop_returned {s u t : ArmState} (stable : LoopStable s u)
    (returned : Returned u t) : Returned s t := by
  refine ⟨returned.pc.trans (stable.registers _ (by decide)), returned.error,
    returned.sp.trans stable.sp, ?_, ?_⟩
  · intro reg low high
    apply (returned.registers reg low high).trans
    apply stable.registers
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    repeat' apply And.intro
    all_goals bv_omega
  · intro reg low high
    exact (returned.vectors reg low high).trans
      (congrArg (fun v : BitVec 128 => v.setWidth 64) (stable.vectors reg))

theorem word_written_head (operand : SszNative.NatOperand) (factor : BitVec 64) :
    (SszNative.NatMul.wordWritten operand factor)[0]?.getD 0#64 =
      operand.words[0]?.getD 0#64 * factor := by
  rw [word_written_first]
  simp

def finishWrites (s : ArmState) (pointer : BitVec 64) (count : Nat) : List Delimited.Span :=
  NatMul.loopWrites (r (.GPR 31#5) s) pointer count ++ valueWrites s

/-- The current first stored limb is extended by every actual loop iteration,
then the actual backward scan and result-store/RET path are executed. -/
theorem finish_run (s : ArmState) (base pointer factor : BitVec 64)
    (operand : SszNative.NatOperand)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (head : LoopHeadAt s base operand.pointer pointer factor operand.words operand.wordCount 1)
    (large : 1 < operand.wordCount)
    (space : NatMul.LoopSpace (r (.GPR 31#5) s) pointer (operand.wordCount + 1))
    (physical : operand.pointer.toNat + 8 * operand.words.length ≤ 2^64)
    (separate : Protected (NatMul.loopWrites (r (.GPR 31#5) s) pointer (operand.wordCount + 1))
      operand.pointer.toNat (8 * operand.words.length))
    (input : NatCompare.Words s operand.pointer operand.words)
    (written : NatCompare.Words s pointer [operand.words[0]?.getD 0#64 * factor])
    (carry : r (.GPR 14#5) s = NatMulProduct.high (operand.words[0]?.getD 0#64) factor)
    (bias : r (.GPR 8#5) s = -BitVec.ofNat 64 (8 * operand.wordCount))
    (output : r (.GPR 10#5) s = pointer)
    (low : r (.GPR 11#5) s = operand.words[0]?.getD 0#64 * factor)
    (width : r (.GPR 12#5) s = BitVec.ofNat 64 (operand.wordCount + 2))
    (owned : NormalizeOwned s pointer (SszNative.NatMul.wordWritten operand factor)) :
    ∃ fuel t, run fuel s = t ∧ Returned s t ∧
      SszNative.NatArithmetic.AddResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
        (.ok (SszNative.NatOperand.fromWords pointer (SszNative.NatMul.wordWritten operand factor))) ∧
      NatCompare.Words t pointer (SszNative.NatMul.wordWritten operand factor) ∧
      MemoryFrame (finishWrites s pointer (operand.wordCount + 1)) s t := by
  obtain ⟨fuel, u, ran, stable, pc, words, changed⟩ := word_loop_runs s base pointer factor operand
    code error aligned head large space physical separate input written carry
  have valueWritesEq : valueWrites u = valueWrites s := by
    simp only [valueWrites, NatAdd.valueWrites, stable.sp, stable.registers 0#5 (by decide)]
  have ready : NormalizeOwned u pointer (SszNative.NatMul.wordWritten operand factor) :=
    ⟨loop_return_owned stable owned.returns, owned.positive, owned.aligned, owned.physical,
      by simpa only [valueWritesEq] using owned.separate⟩
  obtain ⟨last, t, returnedRun, result⟩ := normalize_word_run_contract u base pointer factor operand
    (stable.code code) (stable.error.trans error) (stable.aligned aligned) pc
    ((stable.registers 8#5 (by decide)).trans bias)
    ((stable.registers 10#5 (by decide)).trans output)
    (by rw [stable.registers 11#5 (by decide), low, word_written_head])
    ((stable.registers 12#5 (by decide)).trans width) ready words
  refine ⟨fuel + last, t, by rw [run_plus, ran, returnedRun],
    loop_returned stable result.returned, ?_, result.words, ?_⟩
  · simpa only [stable.registers 0#5 (by decide)] using result.image
  · have before : MemoryFrame (finishWrites s pointer (operand.wordCount + 1)) s u := by
      apply changed.weaken
      intro span member
      exact List.mem_append_left _ member
    have after : MemoryFrame (finishWrites s pointer (operand.wordCount + 1)) u t := by
      apply result.frame.weaken
      intro span member
      rw [valueWritesEq] at member
      exact List.mem_append_right _ member
    exact before.trans after

end SszArm.NatMulWord.Large

import SszArm.SerializeSuccessPathState

namespace SszArm.Serialize.SuccessPath

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value)
open Delimited (MemoryFrame)
open UintCodec (widthLoad)

theorem error_space {s t : ArmState} {desc : Desc} {value : Value}
    (owned : Owned s (Args.ofEntry s) desc value)
    (registers : Registers t (Args.ofEntry s)) : Finish.ErrorSpace t := by
  have low := owned.stackLow
  have stackNat := bodySP_toNat (Args.ofEntry s) (by omega)
  have bound := (Args.ofEntry s).stack.isLt
  have resultBound := owned.resultBound
  have separation := owned.resultStack
  rcases separation with empty | apart
  · contradiction
  · have scratch := apart ((Args.ofEntry s).stack.toNat - 160, 16) (by simp [stackSpans])
    have saved := apart ((Args.ofEntry s).stack.toNat - 48, 48) (by simp [stackSpans])
    constructor <;>
      simp only [Finish.sp, Finish.result, registers.stack, registers.result, stackNat] <;>
      dsimp at scratch saved <;> omega

theorem failure_correct (s t : ArmState) (base : BitVec 64) (desc : Desc) (value : Value)
    (owned : Owned s (Args.ofEntry s) desc value) (ready : Ready s t base desc value)
    (operand : NatOperand)
    (success : (measured s (Args.ofEntry s) desc value).result = .ok operand)
    (kind : Finish.Failure)
    (pc : read_pc t = base + BitVec.ofNat 64 kind.entry)
    (fails : ¬ (operand.value < 2^64 ∧ operand.value ≤ (Args.ofEntry s).capacity.toNat))
    (outcomeEq : outcome s (Args.ofEntry s) desc value =
      ⟨⟨.error .outputTooSmall, (measured s (Args.ofEntry s) desc value).used,
        (measured s (Args.ofEntry s) desc value).calls⟩, #[]⟩) :
    ∃ fuel u, run fuel t = u ∧ Post s u desc value := by
  let args := Args.ofEntry s
  let u := kind.returned base t
  have low : 432 ≤ args.stack.toNat := owned.stackLow
  have stackNat := bodySP_toNat args (by omega)
  have space := error_space owned ready.registers
  have frame : MemoryFrame [(args.stack.toNat - 160, 16), (args.result.toNat, 68)] t u := by
    have liveStack : Finish.sp t = args.bodySP := ready.registers.stack
    have liveResult : Finish.result t = args.result := ready.registers.result
    have position : (Finish.sp t).toNat - 16 = args.stack.toNat - 160 := by
      rw [liveStack, stackNat]
      omega
    have nativeFrame := kind.frame base t space
    rw [position, liveResult] at nativeFrame
    exact nativeFrame
  have covered : Covers [(args.stack.toNat - 160, 16), (args.result.toNat, 68)]
      (stackSpans args ++ externalSpans args) := by
    intro span member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨_, by simp [stackSpans], Nat.le_refl _, Nat.le_refl _⟩
    · refine ⟨(args.result.toNat, 72), by simp [externalSpans], Nat.le_refl _, ?_⟩
      dsimp
      omega
  have resources := Resources.of_frame owned ready.resources frame covered
  have finalFrame : MemoryFrame (writesFor s args desc value) s u := ready.frame.trans
    (frame.weaken (by
      intro span member
      exact List.mem_append.mpr (Or.inr (by
        simp only [continuationWrites, success, fails, ↓reduceIte]
        exact List.mem_append.mpr (Or.inr member)))))
  have returned : Emit.Returned s u :=
    kind.returned_original base s t space ready.saved ready.program ready.error
  refine ⟨kind.ops.length + (2 + 5), u,
    kind.return_run base t ready.code ready.error ready.aligned pc, ?_⟩
  apply post_of_return s u desc value owned returned
  · rw [outcomeEq]
    simpa only [ResultAt, Finish.result, ready.registers.result] using kind.error_at base t space
  · simpa only [outcomeEq] using resources.cursor
  · exact resources.header
  · simpa only [outcomeEq] using resources.written
  · rw [outcomeEq]
    simp [SszNative.ByteView.BytesAt]
  · exact finalFrame

end SszArm.Serialize.SuccessPath

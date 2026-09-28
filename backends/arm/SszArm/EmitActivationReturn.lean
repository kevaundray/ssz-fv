import SszArm.EmitActivationReturnRestore
import SszArm.EmitActivationReturnMemory
import SszArm.EmitEntry
import SszArm.EmitPost

namespace SszArm.Emit

open SszNative.Serialize (Desc Value)
open UintCodec (widthLoad)
open Delimited (MemoryFrame)

/-- Derive the original save words after an arbitrary certified primitive body
and the actual success-status lowering. No future saved-memory observation is
assumed: the prologue summary and the exact body/status frames establish it. -/
theorem restore_ready_of_produced {s b t : ArmState} {desc : Desc} {value : Value}
    {size : Nat} {base : BitVec 64}
    (owned : Owned s (Args.ofEntry s) desc value size)
    (routed : Routed s b desc value size base)
    (produced : Produced b t (Args.ofEntry s) desc value size base) :
    RestoreReady s (statusStored t) := by
  have statusFrame := statusStored_frame produced.stack produced.resultRegister owned.stackLow owned.resultBound
  refine ⟨(statusStored_sp t).trans produced.stack, ?_, ?_, ?_⟩
  · intro reg offset member
    rw [saved_word_preserved statusFrame owned.stackLow (saved_protected_status owned) reg offset member]
    rw [saved_word_preserved produced.frame owned.stackLow (saved_protected_body owned) reg offset member]
    exact routed.saved reg offset member
  · intro reg member
    have not9 : reg ≠ 9#5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide
    have not10 : reg ≠ 10#5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide
    have notSP : reg ≠ 31#5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide
    rw [statusStored_register t reg not9 not10 notSP, produced.registers reg member]
    exact routed.untouched reg member
  · intro reg low high
    rw [statusStored_vector, produced.vectors reg low high, routed.vectors reg]

/-- Execute the seventeen real common success instructions, including lowering,
five restore pairs, ADD SP160 and RET through the original LR. The complete
caller postcondition is recovered from original static ownership. -/
theorem finish_produced {s b t : ArmState} {desc : Desc} {value : Value}
    {size : Nat} {base : BitVec 64}
    (owned : Owned s (Args.ofEntry s) desc value size)
    (routed : Routed s b desc value size base)
    (produced : Produced b t (Args.ofEntry s) desc value size base) :
    run 17 t = returned t ∧ Post s (returned t) desc value size := by
  have code : CodeAt t base := by simpa only [CodeAt, produced.program] using routed.code
  have aligned : CheckSPAlignment t := by
    have aligned := routed.aligned
    simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
      produced.stack, routed.registers.stack] using aligned
  have statusFrame := statusStored_frame produced.stack produced.resultRegister owned.stackLow owned.resultBound
  have ready := restore_ready_of_produced owned routed produced
  have finalMemory : (returned t).mem = (statusStored t).mem := restored_memory _
  have finalFrame : MemoryFrame (writesFor (Args.ofEntry s) size) s (returned t) := by
    have bodyFrame := (routed.frame.weaken (stackWrites_subset _ _)).trans
      (produced.frame.weaken (bodyWrites_subset _ _))
    have statusFrame' := bodyFrame.trans (statusFrame.weaken (statusWrites_subset _ _))
    intro address outside
    rw [finalMemory]
    exact statusFrame' address outside
  refine ⟨returned_run t base code produced.error aligned produced.pc, ?_⟩
  apply post_of_return s (returned t) desc value size owned
  · exact restored_returns s (statusStored t) ready
      ((statusStored_error t).trans produced.error)
      ((statusStored_program t).trans (produced.program.trans routed.program))
  · rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp finalMemory)]
    rw [statusFrame.read _ 8 (by have bound := owned.resultBound; omega) (length_protected_status owned)]
    exact produced.length
  · rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp finalMemory)]
    simpa only [produced.resultRegister] using
      statusStored_status t (by simpa only [produced.resultRegister] using owned.resultBound)
  · rw [load_eq_of_mem_eq finalMemory]
    have exactSize := (SszNative.Serialize.expected_encoding desc value).2 size owned.expected
    apply statusFrame.bytes _ _
    · rw [exactSize]
      have bound := owned.outputBound
      have fits := owned.fitting
      omega
    · rw [exactSize]
      exact output_protected_status owned
    · exact produced.bytes
  · exact finalFrame

end SszArm.Emit

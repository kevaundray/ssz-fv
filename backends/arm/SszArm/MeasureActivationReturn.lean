import SszArm.MeasureActivationReturnRestore
import SszArm.MeasureActivationReturnMemory
import SszArm.MeasureEntry
import SszArm.MeasureAllocationFrame

namespace SszArm.Measure

open SszNative.Serialize (Desc Value)
open UintCodec (widthLoad)
open Delimited (MemoryFrame)

/-- Recover every original save from the actual prologue and the exact body
frame, including allocations retained on an error. No future save-memory premise
is imposed on original ownership or on the body correctness theorem. -/
theorem restore_ready_of_produced {s b t : ArmState} {desc : Desc} {value : Value}
    {base : BitVec 64}
    (owned : Owned s (Args.ofEntry s) desc value)
    (routed : Routed s b desc value base)
    (produced : Produced b t (Args.ofEntry s) desc value base) : RestoreReady s t := by
  have bodyFrame : MemoryFrame (bodyWrites (Args.ofEntry s) (outcome s (Args.ofEntry s) desc value)) b t := by
    simpa only [routed.outcome] using produced.frame
  refine ⟨produced.stack, ?_, ?_, ?_⟩
  · intro reg offset member
    rw [saved_word_preserved bodyFrame owned.stackLow (saved_protected_body owned) reg offset member]
    exact routed.saved reg offset member
  · intro reg member
    have included : reg ∈ [18#5, 27#5, 28#5, 29#5] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      rcases member with h | h | h <;> simp [h]
    rw [produced.registers reg included, routed.untouched reg included]
  · intro reg low high
    rw [produced.vectors reg low high, routed.vectors reg]

theorem Routed.header {s b : ArmState} {desc : Desc} {value : Value} {base : BitVec 64}
    (routed : Routed s b desc value base) :
    read_mem_bytes 8 (Args.ofEntry s).arena b = read_mem_bytes 8 (Args.ofEntry s).arena s ∧
    read_mem_bytes 8 ((Args.ofEntry s).arena + 8#64) b =
      read_mem_bytes 8 ((Args.ofEntry s).arena + 8#64) s := by
  constructor
  · apply BitVec.eq_of_toNat_eq
    exact congrArg (fun arena : SszNative.Delimited.ArenaState => arena.base) routed.arena
  · apply BitVec.eq_of_toNat_eq
    exact congrArg (fun arena : SszNative.Delimited.ArenaState => arena.capacity) routed.arena

/-- The complete result, exact cursor and ordered allocations survive the seven
real epilogue instructions, through RET to the original LR and the full ABI. -/
theorem finish_produced {s b t : ArmState} {desc : Desc} {value : Value} {base : BitVec 64}
    (owned : Owned s (Args.ofEntry s) desc value)
    (routed : Routed s b desc value base)
    (produced : Produced b t (Args.ofEntry s) desc value base) :
    run 7 t = restored t ∧ Post s (restored t) desc value := by
  have code : CodeAt t base := routed.code.congr produced.program
  have aligned : CheckSPAlignment t := by
    have aligned := routed.aligned
    simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
      produced.stack, routed.registers.stack] using aligned
  have bodyFrame : MemoryFrame (bodyWrites (Args.ofEntry s) (outcome s (Args.ofEntry s) desc value)) b t := by
    simpa only [routed.outcome] using produced.frame
  have finalFrame : MemoryFrame (writesFor (Args.ofEntry s) (outcome s (Args.ofEntry s) desc value)) s (restored t) := by
    have throughBody := (routed.frame.weaken (saveWrites_subset _ _)).trans
      (bodyFrame.weaken (bodyWrites_subset _ _))
    intro address outside
    rw [restored_memory]
    exact throughBody address outside
  refine ⟨restored_run t base code produced.error aligned produced.pc, ?_⟩
  refine ⟨restored_returns s t (restore_ready_of_produced owned routed produced)
    produced.error (produced.program.trans routed.program), ?_, ?_, ?_, ?_, finalFrame,
    descriptor_preserved owned finalFrame, value_preserved owned finalFrame, ?_, ?_⟩
  · rw [Emit.load_eq_of_mem_eq (restored_memory t)]
    simpa only [routed.outcome] using produced.result
  · rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (restored_memory t))]
    simpa only [routed.outcome] using produced.cursor
  · constructor
    · rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (restored_memory t))]
      exact produced.header.1.trans routed.header.1
    · rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp (restored_memory t))]
      exact produced.header.2.trans routed.header.2
  · intro call member
    rw [Emit.load_eq_of_mem_eq (restored_memory t)]
    apply produced.written call
    simpa only [routed.outcome] using member
  · intro operand member
    exact NatDivision.operand_preserved finalFrame operand (owned.operand_at operand member)
      (owned.operandOwned operand member)
  · intro span member address low high
    exact finalFrame.protected_byte (owned.backingOwned span member) address low high

end SszArm.Measure

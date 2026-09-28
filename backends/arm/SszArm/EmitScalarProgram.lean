import SszArm.EmitScalar
import SszArm.EmitActivationReturn

namespace SszArm.Emit

open SszNative.Serialize (Desc Value)

/-- Boolean emission from original private entry, through its real stores and
original-stack RET. The Plan argument remains entirely unconstrained. -/
theorem bool_program_correct (s : ArmState) (base : BitVec 64) (flag : Bool) (size : Nat)
    (owned : Owned s (Args.ofEntry s) .bool (.bool flag) size)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) : ∃ fuel, Post s (run fuel s) .bool (.bool flag) size := by
  obtain ⟨entryRun, entryPost⟩ := entry_to_body s base .bool (.bool flag) size owned code error aligned pc
  obtain ⟨steps, t, bodyRun, bodyPost⟩ := bool_body (routed s .bool) base (Args.ofEntry s) flag size
    entryPost.owned entryPost.registers entryPost.code entryPost.error entryPost.aligned
    (by simpa only [bodyEntry] using entryPost.pc)
    (by exact entryPost.valueTag)
  obtain ⟨returnRun, post⟩ := finish_produced owned entryPost bodyPost
  refine ⟨(12 + (dispatchOps Desc.bool).length) + (steps + 17), ?_⟩
  rw [run_plus, entryRun, run_plus, bodyRun, returnRun]
  exact post

/-- Both byte descriptor kinds execute the same real memcpy branch, from entry0
through the linked helper and original LR return, including an empty copy. -/
theorem bytes_program_correct (s : ArmState) (base : BitVec 64) (desc : Desc)
    (bytes : Ssz.Bytes) (size : Nat) (kind : Scalar.ByteKind desc)
    (owned : Owned s (Args.ofEntry s) desc (.bytes bytes) size)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) : ∃ fuel, Post s (run fuel s) desc (.bytes bytes) size := by
  obtain ⟨entryRun, entryPost⟩ := entry_to_body s base desc (.bytes bytes) size owned code error aligned pc
  have bodyPC : read_pc (routed s desc) = base + 820#64 := by
    obtain ⟨operand, rfl | rfl⟩ := kind <;> exact entryPost.pc
  obtain ⟨steps, t, bodyRun, bodyPost⟩ := Scalar.bytes_body (routed s desc) base (Args.ofEntry s)
    desc bytes size kind entryPost.owned entryPost.registers entryPost.code entryPost.error
    entryPost.aligned bodyPC entryPost.tag
  obtain ⟨returnRun, post⟩ := finish_produced owned entryPost bodyPost
  refine ⟨(12 + (dispatchOps desc).length) + (steps + 17), ?_⟩
  rw [run_plus, entryRun, run_plus, bodyRun, returnRun]
  exact post

end SszArm.Emit

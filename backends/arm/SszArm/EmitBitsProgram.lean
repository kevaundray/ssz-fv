import SszArm.EmitBits
import SszArm.EmitActivationReturn

namespace SszArm.Emit

open SszNative.Serialize (Desc Packed)

/-- All packed-bit kinds execute their real linked copy, masked or delimited
suffix, length/status stores, and original-stack return from the private entry. -/
theorem bits_program_correct (s : ArmState) (base : BitVec 64) (desc : Desc)
    (bits : Packed) (size : Nat) (kind : Bits.IsBits desc)
    (owned : Owned s (Args.ofEntry s) desc (.bits bits) size)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) : ∃ fuel, Post s (run fuel s) desc (.bits bits) size := by
  obtain ⟨entryRun, entryPost⟩ := entry_to_body s base desc (.bits bits) size owned code error aligned pc
  have bodyPC : read_pc (routed s desc) = base + 568#64 := by
    cases desc <;> simp only [Bits.IsBits] at kind <;> try contradiction
    all_goals exact entryPost.pc
  obtain ⟨steps, t, bodyRun, bodyPost⟩ := Bits.body_correct (routed s desc) base (Args.ofEntry s)
    desc bits size kind entryPost.owned entryPost.registers entryPost.code entryPost.error
    entryPost.aligned bodyPC entryPost.tag
  obtain ⟨returnRun, post⟩ := finish_produced owned entryPost bodyPost
  refine ⟨(12 + (dispatchOps desc).length) + (steps + 17), ?_⟩
  rw [run_plus, entryRun, run_plus, bodyRun, returnRun]
  exact post

end SszArm.Emit

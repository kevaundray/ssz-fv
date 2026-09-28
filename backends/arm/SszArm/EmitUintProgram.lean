import SszArm.EmitUintBody
import SszArm.EmitActivationReturn

namespace SszArm.Emit

open SszNative (NatOperand)

/-- Original private entry through the padded-width scan, arbitrary-width byte
loop, success status lowering and real RET using the caller's saved LR/SP. -/
theorem uint_program_correct (s : ArmState) (base : BitVec 64) (width number : NatOperand) (size : Nat)
    (owned : Owned s (Args.ofEntry s) (.uint width) (.uint number) size)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) :
    ∃ fuel, Post s (run fuel s) (.uint width) (.uint number) size := by
  obtain ⟨entryRun, entryPost⟩ :=
    entry_to_body s base (.uint width) (.uint number) size owned code error aligned pc
  obtain ⟨steps, t, bodyRun, bodyPost⟩ :=
    Uint.body_correct (routed s (.uint width)) base (Args.ofEntry s) width number size
      entryPost.code entryPost.owned entryPost.registers entryPost.error entryPost.aligned
      (by simpa only [bodyEntry] using entryPost.pc) entryPost.descriptor
      (by simpa [valueTag] using entryPost.valueTag)
  obtain ⟨returnRun, post⟩ := finish_produced owned entryPost bodyPost
  refine ⟨(12 + (dispatchOps (.uint width)).length) + (steps + 17), ?_⟩
  rw [run_plus, entryRun, run_plus, bodyRun, returnRun]
  exact post

end SszArm.Emit

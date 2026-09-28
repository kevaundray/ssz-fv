import SszArm.BitVectorScopeCall

namespace SszArm.BitVector

open UintCodec (widthLoad)

theorem scope_success_branch {s c d : ArmState} {length expected : SszNative.NatOperand}
    {data : Ssz.Bytes} {remainder : BitVec 64} (base : BitVec 64)
    (owned : Owned s length data) (atCall : Working s c length)
    (current : Counted s d length remainder) (post : NatExact.Post (scopeEntry c base) d expected)
    (accepted : SszNative.NatNarrow.runExact expected (BitVec.ofNat 64 data.size) = true)
    (code : JointCodeAt d base) (aligned : CheckSPAlignment s)
    (pc : read_pc d = base + 5964#64) :
    run 2 d = ExpectedStage.Stage.scope.result d base ∧
      read_pc (ExpectedStage.Stage.scope.result d base) = base + 6000#64 := by
  have args := scope_arguments base owned atCall
  have stored := post.result
  rw [args.1, args.2.2] at stored
  simp only [SszNative.NatNarrow.ExactResultAt, accepted, ↓reduceIte] at stored
  have status : read_mem_bytes 4 (r (.GPR 31#5) s + 208#64) d = 0#32 := by
    simpa only [BitVec.add_assoc, show 144#64 + 64#64 = 208#64 by decide] using
      read_of_observe_offset d (r (.GPR 31#5) s + 144#64) 64 4 0#32 stored
  refine ⟨ExpectedStage.executes .scope d base code.body current.error
    (current.toWorking.aligned aligned) pc, ?_⟩
  simp (config := {decide := true}) only [ExpectedStage.Stage.result, state_simp_rules,
    current.sp, status, show (0#32 : BitVec 32) = 0 by rfl, if_pos]

end SszArm.BitVector

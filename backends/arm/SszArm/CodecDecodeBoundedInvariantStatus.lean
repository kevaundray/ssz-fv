import SszArm.CodecDecodeBoundedInvariantMemory
import SszArm.CodecDecodeBoundedErrorFinish

namespace SszArm.Codec.Decode.Bounded

open SszNative
open Delimited (MemoryFrame)

theorem Owned.errorSpace {s t : ArmState} {limit : Option NatOperand} {actual : NatOperand}
    (owned : Owned s limit actual) (active : Activation s t)
    (output : r (.GPR 19#5) t = r (.GPR 0#5) s) : ErrorSpace t := by
  have low := owned.stackBound
  have bound := owned.resultBound
  refine ⟨?_, by simpa only [output] using bound, ?_⟩
  · rw [active.stack]
    simp only [bodySP]
    bv_omega
  · rcases owned.outputStack with empty | separate
    · omega
    have apart := separate ((r (.GPR 31#5) s).toNat - 64, 16) (by simp [stackWrites])
    simp only [Prod.fst, Prod.snd] at apart
    rw [active.stack, output]
    simp only [bodySP]
    bv_omega

theorem status_local_frame (s : ArmState) (space : ErrorSpace s) :
    MemoryFrame (errorWrites s) s (Emit.statusStored s) := by
  have frame := status_frame s space.stack space.output
  intro address outside
  apply frame address
  intro span member
  simp only [statusWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact outside _ (by simp [errorWrites])
  · have output := outside ((r (.GPR 19#5) s).toNat, 68) (by simp [errorWrites])
    simp only [Prod.fst, Prod.snd] at output ⊢
    omega

theorem Activation.status {s t : ArmState} {limit : Option NatOperand} {actual : NatOperand}
    (owned : Owned s limit actual) (active : Activation s t)
    (output : r (.GPR 19#5) t = r (.GPR 0#5) s) : Activation s (Emit.statusStored t) := by
  apply active.written owned output (status_local_frame t (owned.errorSpace active output))
    (Emit.statusStored_sp t)
  · intro reg low high outside
    exact Emit.statusStored_register t reg (by bv_omega) (by bv_omega) (by bv_omega)
  · exact Emit.statusStored_vector t
  · exact Emit.statusStored_program t
  · exact Emit.statusStored_error t

theorem Activation.error_stage {s t : ArmState} {limit : Option NatOperand} {actual : NatOperand}
    (owned : Owned s limit actual) (active : Activation s t)
    (output : r (.GPR 19#5) t = r (.GPR 0#5) s) (stage : ErrorStage) (base : BitVec 64) :
    Activation s (stage.result t base) := by
  have space := owned.errorSpace active output
  apply active.written owned output (error_stage_frame stage t base space.stack space.output)
    (error_stage_sp stage t base)
  · intro reg low high outside
    apply error_stage_register
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    constructor
    · bv_omega
    · constructor
      · bv_omega
      · constructor <;> bv_omega
  · exact error_stage_vector stage t base
  · exact error_stage_program stage t base
  · exact error_stage_error stage t base

end SszArm.Codec.Decode.Bounded

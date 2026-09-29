import SszArm.CodecDecodeBoundedInvariantStatus
import SszArm.CodecDecodeBoundedCall

namespace SszArm.Codec.Decode.Bounded

open SszNative
open Delimited (MemoryFrame)

theorem Activation.prepared {s t : ArmState} (active : Activation s t) (base : BitVec 64) :
    Activation s (prepared t base) := by
  apply active.readonly (prepared_memory t base) (prepared_sp t base)
  · intro reg low high outside
    have h0 : reg ≠ 0#5 := by bv_omega
    have h1 : reg ≠ 1#5 := by bv_omega
    have h2 : reg ≠ 2#5 := by bv_omega
    have h3 : reg ≠ 3#5 := by bv_omega
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    simp (disch := simp_all) [prepared, state_simp_rules, h0, h1, h2, h3]
  · intro reg
    simp [prepared, state_simp_rules]
  · exact prepared_program t base
  · simp [prepared, state_simp_rules]

theorem compare_local_frame {s t : ArmState} (frame : NatCompare.Frame s t)
    (low : 16 ≤ (r (.GPR 31#5) s).toNat) : MemoryFrame (errorWrites s) s t := by
  intro address outside
  have apart := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [errorWrites])
  simp only [Prod.fst, Prod.snd] at apart
  apply frame.memory
  omega

theorem Activation.compared {s t u : ArmState} {limit : Option NatOperand} {actual : NatOperand}
    (owned : Owned s limit actual) (active : Activation s t)
    (output : r (.GPR 19#5) t = r (.GPR 0#5) s) (frame : NatCompare.Frame t u) :
    Activation s u := by
  apply active.written owned output
    (compare_local_frame frame (owned.errorSpace active output).stack) frame.sp
  · intro reg low high outside
    apply frame.registers
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    repeat' constructor
    all_goals bv_omega
  · exact frame.vectors
  · exact frame.program
  · exact frame.error

end SszArm.Codec.Decode.Bounded

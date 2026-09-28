import SszArm.SerializeErrorPath
import SszArm.SerializeSuccessPath
import SszArm.SerializePost

namespace SszArm.Serialize

open SszNative.Serialize (Desc Value)
open UintCodec (widthLoad)

/-- The original private wrapper, including both real BL instructions and its
original-LR RET. Measurement errors precede host narrowing, which precedes the
output-capacity guard. No initialized Plan/output, successful sizing, future
callee ownership, helper exit, or future execution is assumed. -/
theorem program_correct (s : ArmState) (base : BitVec 64) (desc : Desc) (value : Value)
    (owned : Owned s (Args.ofEntry s) desc value)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Post s t desc value := by
  obtain ⟨firstFuel, m, firstRun, measurement⟩ :=
    measurement_correct s base desc value owned code error aligned pc
  cases checked : (measured s (Args.ofEntry s) desc value).result with
  | error reason =>
    obtain ⟨restFuel, t, restRun, post⟩ :=
      measurement_error_correct s m base desc value owned measurement reason checked
    refine ⟨firstFuel + restFuel, t, ?_, post⟩
    rw [run_plus, firstRun, restRun]
  | ok operand =>
    obtain ⟨restFuel, t, restRun, post⟩ :=
      measurement_success_correct s m base desc value owned measurement operand checked
    refine ⟨firstFuel + restFuel, t, ?_, post⟩
    rw [run_plus, firstRun, restRun]

/-- Pinned SSZ correspondence with the full resource-sensitive physical post.
Scratch exhaustion and host/output-capacity failure remain explicit alternatives;
Post retains their exact cursor, ordered constructor calls and empty output. -/
theorem program_refines (s : ArmState) (base : BitVec 64) (desc : Desc) (value : Value)
    (owned : Owned s (Args.ofEntry s) desc value)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Post s t desc value ∧
      ∃ result writes,
        ResultAt (widthLoad t) (Args.ofEntry s).result.toNat result ∧
        SszNative.ByteView.BytesAt (widthLoad t) (Args.ofEntry s).output.toNat writes ∧
        (SszNative.Serialize.eraseResult (result.map (fun _ => writes)) =
            .ok (Ssz.serialize desc.erase value.erase) ∨
          result = .error (.arithmetic .scratchExhausted) ∨
          result = .error .outputTooSmall) := by
  obtain ⟨fuel, t, executed, post⟩ := program_correct s base desc value owned code error aligned pc
  exact ⟨fuel, t, executed, post, post.refines owned.physical⟩

end SszArm.Serialize

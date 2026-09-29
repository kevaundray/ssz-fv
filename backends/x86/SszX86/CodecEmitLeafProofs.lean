import SszX86.CodecEmitLeafExec
import SszX86.CodecEmitLeafFinishMemory

set_option autoImplicit false

namespace SszX86.CodecEmit
open SszNative

variable {s body final : MachineData} {base : Int64} {shape : Serialize.Desc}
  {value : SszNative.Codec.Value} {supplied : Option SszNative.CodecMeasure.Plan}
  {r : SszX86.Codec.Footprint} {ra : BitVec 64}

theorem leaf_return_post (anchors : Emit.AtBody s body)
    (owned : Owned s base (.primitive shape) value supplied r ra)
    (post : Emit.BodyPost body (Serialize.emit shape value.toPrimitive) final) :
    Post s (.primitive shape) value supplied ra owned.call.measured.size.value
      (Emit.returned (Emit.successState final) (Emit.saved s ra), Int64.ofBitVec ra) := by
  have memory := leaf_success_memory anchors owned post
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, memory.length, memory.status,
    leaf_output_trace owned memory, memory.frame⟩
  · change final.regs.rsp.toBitVec + 160#64 = s.regs.rsp.toBitVec + 8
    rw [post.stack, anchors.stack]
    bv_omega
  · exact post.vector.trans anchors.vector

theorem leaf_finish_runs (e : Executable) (base : Int64) (code : CodeAt e base)
    (s body final : MachineData) (shape : Serialize.Desc) (value : SszNative.Codec.Value)
    (supplied : Option SszNative.CodecMeasure.Plan) (r : SszX86.Codec.Footprint) (ra : BitVec 64)
    (owned : Owned s base (.primitive shape) value supplied r ra) (anchors : Emit.AtBody s body)
    (post : Emit.BodyPost body (Serialize.emit shape value.toPrimitive) final) :
    Eventually (step e) (Post s (.primitive shape) value supplied ra owned.call.measured.size.value)
      (final, base + 1593) := by
  apply Emit.status_runs e base code.primitive final _ (status_current anchors owned post)
  apply Emit.epilogue e base code.primitive (Emit.successState final) (Emit.saved s ra)
    (saved_success anchors owned post)
  exact leaf_return_post anchors owned post

/-- Actual complete emitter entry through its caller RET for every generated
primitive plan, now under the recursive owner's exact 72-byte result contract.
The proof reuses immutable body instruction providers and derives their safety
from the past measured plan; no schema-validation or future-run premise occurs. -/
theorem leaf_program_correct (e : Executable) (base : Int64) (code : CodeAt e base)
    (copy : Emit.MemcpyCodeAt e (base + 110736))
    (s : MachineData) (shape : Serialize.Desc) (value : SszNative.Codec.Value)
    (supplied : Option SszNative.CodecMeasure.Plan) (r : SszX86.Codec.Footprint) (ra : BitVec 64)
    (owned : Owned s base (.primitive shape) value supplied r ra) :
    Eventually (step e) (Post s (.primitive shape) value supplied ra owned.call.measured.size.value)
      (s, base) := by
  apply eventually_trans (step e) _ _ _
    (leaf_entry_correct e base code s shape value supplied r ra owned)
  rintro ⟨body, pc⟩ ⟨entryPC, anchors, tag⟩
  dsimp only at entryPC
  subst pc
  obtain ⟨buffer, resources⟩ := leaf_resources owned anchors tag
  apply eventually_trans (step e) _ _ _
    (leaf_body_correct e base code copy body shape value supplied r buffer
      (callAtBody owned anchors) resources)
  rintro ⟨final, pc⟩ ⟨successPC, post⟩
  dsimp only at successPC
  subst pc
  exact leaf_finish_runs e base code s body final shape value supplied r ra owned anchors post

end SszX86.CodecEmit

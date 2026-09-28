import SszX86.EmitPost

namespace SszX86.Emit
open SszNative.Serialize

theorem AtBody.return_post {s body final : MachineData} {base : Int64}
    {desc : Desc} {value : Value} {buffer ra : BitVec 64} {written : Nat}
    (h : AtBody s body) (owned : Owned s base desc value buffer ra written)
    (post : BodyPost body (emit desc value) final) :
    Post s desc value buffer ra written
      (returned (successState final) (saved s ra), Int64.ofBitVec ra) := by
  have memory := h.success_memory owned post
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, memory,
    memory.output_frame owned, memory.result_frame owned, memory.borrowed_frame owned⟩
  · change final.regs.rsp.toBitVec + 160#64 = s.regs.rsp.toBitVec + 8
    rw [post.stack, h.stack]
    bv_omega
  · exact post.vector.trans h.vector

/-- The common status store followed by actual ADD104, six POPs, and RET.
All saved words and the status-store mapping are derived from entry ownership. -/
theorem finish_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s body final : MachineData) (desc : Desc) (value : Value)
    (buffer ra : BitVec 64) (written : Nat)
    (owned : Owned s base desc value buffer ra written) (entry : AtBody s body)
    (post : BodyPost body (emit desc value) final) :
    Eventually (step e) (Post s desc value buffer ra written) (final, base + 1593) := by
  apply status_runs e base hc final _ (entry.status_current owned post)
  apply epilogue e base hc (successState final) (saved s ra)
    (entry.saved_success owned post)
  exact entry.return_post owned post

end SszX86.Emit

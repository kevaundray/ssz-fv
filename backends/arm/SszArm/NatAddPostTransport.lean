import SszArm.NatAddTransport

namespace SszArm.NatAdd

open Delimited (MemoryFrame Returned)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Prepend an actual width/borrow scan to a complete return certificate.
The original arena, output address, operands, byte frame and ABI are retained. -/
theorem Post.prepend {s u : ArmState} {left right : SszNative.NatOperand}
    (owned : Owned s left right) (frame : NatCompare.Frame s u)
    (out : r (.GPR 0#5) u = r (.GPR 0#5) s)
    (fuel : Nat) (execution : run fuel s = u)
    (tail : ∃ steps t, run steps u = t ∧ Post u t left right) :
    ∃ steps t, run steps s = t ∧ Post s t left right := by
  obtain ⟨steps, t, ran, post⟩ := tail
  have result := outcome_eq_of_scan owned frame
  have writes := writesFor_eq_of_scan owned frame out
  have arena := frame.registers 5#5 (by decide)
  have returned : Returned s t := by
    refine ⟨post.returned.pc.trans (frame.registers 30#5 (by decide)),
      post.returned.error, post.returned.sp.trans frame.sp, ?_, ?_⟩
    · intro reg low high
      apply (post.returned.registers reg low high).trans
      apply frame.registers
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      repeat constructor <;> bv_omega
    · intro reg low high
      rw [post.returned.vectors reg low high, frame.vectors]
  refine ⟨fuel + steps, t, ?_, ?_⟩
  · rw [run_plus, execution, ran]
  · apply post_of_frame s t left right owned returned
    · simpa only [out, result] using post.result
    · simpa only [result] using post.written
    · simpa only [arena, result] using post.cursor
    · apply (local_frame _ (scan_memory frame owned.stackBound)).trans
      simpa only [writes] using post.frame

end SszArm.NatAdd

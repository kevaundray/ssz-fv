import SszArm.MeasureBitsReturnedPost

namespace SszArm.Measure.Bits

open Propagation

private theorem returned_vector_nonzero (reg : BitVec 5) (low : 8 ≤ reg.toNat) :
    reg ≠ 0#5 := by
  intro same
  have zero : reg.toNat = 0 := by
    simpa only [same] using (show (0#5).toNat = 0 by decide)
  omega

theorem returned_error_post (s p t : ArmState) (base : BitVec 64)
    (post : ErrorPost p t base)
    (program : p.program = s.program) (memory : p.mem = s.mem)
    (output : r (.GPR 19#5) p = r (.GPR 19#5) s)
    (stack : r (.GPR 31#5) p = r (.GPR 31#5) s)
    (registers : ∀ reg : BitVec 5, reg ∈ [18#5, 27#5, 28#5, 29#5] →
      r (.GPR reg) p = r (.GPR reg) s)
    (vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
      (r (.SFP reg) p).setWidth 64 = (r (.SFP reg) s).setWidth 64) :
    ReturnedPost s t base (.error (.arithmetic .scratchExhausted))
      [((r (.GPR 19#5) s).toNat, 72)] := by
  refine ⟨post.pc, post.program.trans program, post.error,
    (post.registers 31#5 (by decide)).trans stack, ?_, ?_, ?_, ?_⟩
  · simpa only [output] using post.result
  · intro address outside
    have last := post.frame address (by simpa only [output] using outside)
    exact last.trans (congrFun memory address)
  · intro reg member
    have keep : reg ∉ [0#5, 1#5, 2#5, 3#5, 4#5, 8#5, 30#5] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    exact (post.registers reg keep).trans (registers reg member)
  · intro reg low high
    exact (congrArg (fun value : BitVec 128 => value.setWidth 64)
      (post.vectors reg (returned_vector_nonzero reg low))).trans (vectors reg low high)

end SszArm.Measure.Bits

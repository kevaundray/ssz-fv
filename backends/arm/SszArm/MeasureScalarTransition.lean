import SszArm.MeasureResultProduced

namespace SszArm.Measure.Scalar

open SszNative.Serialize (Desc Value)

/-- Register-only routing and leaf prefixes do not change the measurement's
original storage observations or the exact allocation trace. -/
theorem prepend_pure {s u t : ArmState} {args : Args} {desc : Desc} {value : Value}
    {base : BitVec 64} (post : Produced u t args desc value base)
    (program : u.program = s.program) (memory : u.mem = s.mem)
    (registers : ∀ reg : BitVec 5, reg ∈ [18#5, 27#5, 28#5, 29#5] →
      r (.GPR reg) u = r (.GPR reg) s)
    (vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
      (r (.SFP reg) u).setWidth 64 = (r (.SFP reg) s).setWidth 64) :
    Produced s t args desc value base := by
  have reads : ∀ bytes address, read_mem_bytes bytes address u = read_mem_bytes bytes address s := by
    intro bytes address
    apply BoolCodec.read_bytes_congr
    intro i inside
    change u.mem _ = s.mem _
    rw [memory]
  have measured : outcome u args desc value = outcome s args desc value := by
    simp only [outcome, arenaOf, reads]
  refine ⟨post.pc, post.program.trans program, post.error, post.stack,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [measured] using post.result
  · simpa only [measured] using post.cursor
  · simpa only [reads] using post.header
  · simpa only [measured] using post.written
  · intro address outside
    rw [post.frame address (by simpa only [measured] using outside), memory]
  · intro reg member
    exact (post.registers reg member).trans (registers reg member)
  · intro reg low high
    exact (post.vectors reg low high).trans (vectors reg low high)

end SszArm.Measure.Scalar

import SszArm.MeasureOwnership

namespace SszArm.Measure

open SszNative.Serialize (Desc Value)

/-- A real lowering-slot prefix precedes a leaf summary without changing the
logical arena input. Unlike a pure prefix, its saved register bytes remain in
final memory and therefore participate in the body's frame. -/
theorem Produced.prepend_stack {s u t : ArmState} {args : Args} {desc : Desc} {value : Value}
    {base : BitVec 64} (post : Produced u t args desc value base)
    (owned : Owned s args desc value)
    (frame : Delimited.MemoryFrame (bodyStackWrites args (outcome s args desc value)) s u)
    (program : u.program = s.program)
    (registers : ∀ reg : BitVec 5, reg ∈ [18#5, 27#5, 28#5, 29#5] →
      r (.GPR reg) u = r (.GPR reg) s)
    (vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
      (r (.SFP reg) u).setWidth 64 = (r (.SFP reg) s).setWidth 64) :
    Produced s t args desc value base := by
  have localFrame : Delimited.MemoryFrame (localWrites args (outcome s args desc value)) s u :=
    frame.weaken (by
      intro span member
      simp only [localWrites, stackWrites, List.mem_append]
      exact Or.inl (Or.inr member))
  have same : outcome u args desc value = outcome s args desc value :=
    outcome_eq_of_arena_eq (arenaOf_eq_of_local_frame owned localFrame)
  have r0 := Emit.frame_read_offset localFrame args.arena 24 0 8 owned.arenaBound
    owned.headerLocal (by decide)
  have r8 := Emit.frame_read_offset localFrame args.arena 24 8 8 owned.arenaBound
    owned.headerLocal (by decide)
  simp only [BitVec.add_zero] at r0
  refine ⟨post.pc, post.program.trans program, post.error, post.stack, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · simpa only [same] using post.result
  · simpa only [same] using post.cursor
  · exact ⟨post.header.1.trans r0, post.header.2.trans r8⟩
  · simpa only [same] using post.written
  · have bodyFrame : Delimited.MemoryFrame (bodyWrites args (outcome s args desc value)) s u :=
      frame.weaken (by
        intro span member
        simp only [bodyWrites, List.mem_append]
        exact Or.inl (Or.inl member))
    intro address outside
    exact (post.frame address (by simpa only [same] using outside)).trans
      (bodyFrame address outside)
  · intro reg member
    exact (post.registers reg member).trans (registers reg member)
  · intro reg low high
    exact (post.vectors reg low high).trans (vectors reg low high)

end SszArm.Measure

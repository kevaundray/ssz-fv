import SszArm.MeasureHelpersFramePost

namespace SszArm.Measure.Helpers

private theorem called_constructor_owned (s : ArmState) (base : BitVec 64)
    (owned : NatFromU128.Owned s) : NatFromU128.Owned (called .constructWidth s base) := by
  constructor
  · constructor
    · simpa [called, state_simp_rules] using owned.stack
    · simpa [called, state_simp_rules] using owned.output
    · simpa [called, state_simp_rules] using owned.separate
  · simpa [called, state_simp_rules] using owned.header
  · simpa [NatFromU128.addressWord, NatFromU128.capacityWord,
      called, state_simp_rules] using owned.storage
  · simpa [NatFromU128.addressWord, NatFromU128.capacityWord,
      called, state_simp_rules] using owned.nonnull
  · simpa [NatFromU128.localWrites, called, state_simp_rules] using owned.headerLocal
  · simpa [NatFromU128.localWrites, NatFromU128.addressWord,
      NatFromU128.capacityWord, NatFromU128.usedWord,
      called, state_simp_rules] using owned.free

/-- The actual BL1912 and the complete real constructor return. This additionally
exports the x18 and code observations required by the enclosing measure ABI. -/
theorem constructor_correct_frame (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 1912#64)
    (owned : NatFromU128.Owned s) :
    ∃ fuel t, run fuel s = t ∧ NatFromU128.Post (called .constructWidth s base) t ∧
      read_pc t = base + 1916#64 ∧ t.program = s.program ∧
      r (.GPR 18#5) t = r (.GPR 18#5) s := by
  let c := called .constructWidth s base
  have code' : NatFromU128.CodeAt c (base + fromU128Offset) :=
    (code.congr (called_program _ _ _)).fromU128
  have error' : read_err c = .None := (called_error _ _ _).trans error
  have aligned' : CheckSPAlignment c := by
    simpa [c, CheckSPAlignment, called, state_simp_rules] using aligned
  obtain ⟨fuel, t, runs, post, program, platform⟩ :=
    ConstructorFrame.correct c (base + fromU128Offset) code' error' aligned'
      (by simp [c, CallSite.target]) (called_constructor_owned s base owned)
  refine ⟨fuel + 1, t, ?_, post, ?_, program.trans (called_program _ _ _), ?_⟩
  · rw [run, call_step .constructWidth s base code error pc]
    exact runs
  · simpa [c, called, CallSite.offset, state_simp_rules] using post.returned.pc
  · exact platform.trans (called_register _ _ _ 18#5 (by decide))

end SszArm.Measure.Helpers

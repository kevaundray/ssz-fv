import SszArm.MeasureHelpersCalls

namespace SszArm.Measure.Helpers

open UintCodec (widthLoad)

/-- The count bound uses the actual Nat.compare entry and RET, including
arbitrarily padded borrowed operands and the helper's real lowering slot. -/
theorem compare_correct (s : ArmState) (base : BitVec 64) (lhs rhs : Nat)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 1728#64)
    (left : SszNative.NatMemory.Pair (widthLoad s)
      (r (.GPR 0#5) s) (r (.GPR 1#5) s) lhs)
    (right : SszNative.NatMemory.Pair (widthLoad s)
      (r (.GPR 2#5) s) (r (.GPR 3#5) s) rhs)
    (leftOwned : NatCompare.Owned s (r (.GPR 0#5) s) (r (.GPR 1#5) s))
    (rightOwned : NatCompare.Owned s (r (.GPR 2#5) s) (r (.GPR 3#5) s)) :
    ∃ fuel t, run fuel s = t ∧
      NatCompare.Frame (called .compareCount s base) t ∧
      read_pc t = base + 1732#64 ∧
      (r (.GPR 0#5) t).setWidth 8 = SszNative.NatABI.orderingByte (compare lhs rhs) ∧
      SszNative.NatMemory.Pair (widthLoad t)
        (r (.GPR 0#5) s) (r (.GPR 1#5) s) lhs ∧
      SszNative.NatMemory.Pair (widthLoad t)
        (r (.GPR 2#5) s) (r (.GPR 3#5) s) rhs := by
  let c := called .compareCount s base
  have code' : NatCompare.CodeAt c (base + compareOffset) :=
    (code.congr (called_program _ _ _)).compare
  have error' : read_err c = .None := (called_error _ _ _).trans error
  have aligned' : CheckSPAlignment c := by
    simpa [c, CheckSPAlignment, called, state_simp_rules] using aligned
  have left' : SszNative.NatMemory.Pair (widthLoad c)
      (r (.GPR 0#5) c) (r (.GPR 1#5) c) lhs := by
    have observe : widthLoad c = widthLoad s := by
      funext address bytes
      simp only [widthLoad, Memory.State.read_mem_bytes_eq_mem_read_bytes, c, called_memory]
    rw [observe]
    simpa [c, called, state_simp_rules] using left
  have right' : SszNative.NatMemory.Pair (widthLoad c)
      (r (.GPR 2#5) c) (r (.GPR 3#5) c) rhs := by
    have observe : widthLoad c = widthLoad s := by
      funext address bytes
      simp only [widthLoad, Memory.State.read_mem_bytes_eq_mem_read_bytes, c, called_memory]
    rw [observe]
    simpa [c, called, state_simp_rules] using right
  have leftOwned' : NatCompare.Owned c (r (.GPR 0#5) c) (r (.GPR 1#5) c) := by
    simpa [c, NatCompare.Owned, called, state_simp_rules] using leftOwned
  have rightOwned' : NatCompare.Owned c (r (.GPR 2#5) c) (r (.GPR 3#5) c) := by
    simpa [c, NatCompare.Owned, called, state_simp_rules] using rightOwned
  obtain ⟨fuel, t, runs, frame, returned, _, _, _, order, lpair, rpair⟩ :=
    NatCompare.compare_correct c (base + compareOffset) lhs rhs code' error'
      aligned' (by simp [c, CallSite.target, NatCompare.entry])
      left' right' leftOwned' rightOwned'
  refine ⟨fuel + 1, t, ?_, frame, ?_, order, ?_, ?_⟩
  · rw [run, call_step .compareCount s base code error pc]
    exact runs
  · simpa [c, called, CallSite.offset, state_simp_rules] using returned
  · simpa [c, called, state_simp_rules] using lpair
  · simpa [c, called, state_simp_rules] using rpair

private theorem constructor_owned (s : ArmState) (base : BitVec 64)
    (owned : NatFromU128.Owned s) :
    NatFromU128.Owned (called .constructWidth s base) := by
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

/-- Complete actual width construction, not a successful-constructor premise.
The returned Post retains every success and scratch-exhaustion branch. -/
theorem constructor_correct (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 1912#64)
    (owned : NatFromU128.Owned s) :
    ∃ fuel t, run fuel s = t ∧
      NatFromU128.Post (called .constructWidth s base) t ∧
      read_pc t = base + 1916#64 := by
  let c := called .constructWidth s base
  have code' : NatFromU128.CodeAt c (base + fromU128Offset) :=
    (code.congr (called_program _ _ _)).fromU128
  have error' : read_err c = .None := (called_error _ _ _).trans error
  have aligned' : CheckSPAlignment c := by
    simpa [c, CheckSPAlignment, called, state_simp_rules] using aligned
  obtain ⟨fuel, t, runs, post⟩ := NatFromU128.correct c (base + fromU128Offset)
    code' error' aligned' (by simp [c, CallSite.target]) (constructor_owned s base owned)
  refine ⟨fuel + 1, t, ?_, post, ?_⟩
  · rw [run, call_step .constructWidth s base code error pc]
    exact runs
  · simpa [c, called, CallSite.offset, state_simp_rules] using post.returned.pc

end SszArm.Measure.Helpers

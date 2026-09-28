import SszArm.DispatchUintReadonly

namespace SszArm.Dispatch.Unsigned

/-- Original private entry through the real RET, including scope mismatch,
small values, resource exhaustion and arbitrary allocated limb counts. -/
theorem program_correct (s : ArmState) (base : BitVec 64) (width : Nat) (data : Ssz.Bytes)
    (owned : Owned s width data) (dispatch : CodeAt s base) (body : UintCodec.CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Post s t width data := by
  let b := entered s .uint
  have bodyCode : UintCodec.CodeAt b base := by
    simpa only [b, UintCodec.CodeAt, entered_program] using body
  have bodyError : read_err b = .None := by simpa only [b, entered_error] using error
  have bodyPC : read_pc b = base + 148#64 := entered_pc s base .uint owned.scalar.entry pc
  obtain ⟨fuel, t, executed, post⟩ := UintCodec.Body.runs b base width data bodyCode bodyPC
    bodyError (entered_aligned s .uint aligned)
    (by simpa [b] using owned.scalar.descriptorBound) owned.scratch owned.width owned.input owned.body
  refine ⟨Kind.uint.steps + fuel, t, ?_, post_of_body owned post⟩
  rw [run_plus, entry_run s base .uint owned.scalar.entry dispatch error aligned pc]
  exact executed

/-- Resource failure stays distinct from pinned SSZ errors. No availability or
allocation-success premise is required to obtain the full native postcondition. -/
theorem program_refines (s : ArmState) (base : BitVec 64) (width : Nat) (data : Ssz.Bytes)
    (owned : Owned s width data) (dispatch : CodeAt s base) (body : UintCodec.CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Post s t width data ∧
      (if UintCodec.Body.needsAllocation width data ∧ reservation s width data = none then
        SszNative.UintCodec.scratchExhaustedAt (UintCodec.widthLoad t) (r (.GPR 0#5) s).toNat
      else SszNative.UintCodec.ResultAt (UintCodec.widthLoad t) (r (.GPR 0#5) s).toNat
        (Ssz.deserialize (.uint width) data)) := by
  obtain ⟨fuel, t, executed, post⟩ := program_correct s base width data owned dispatch body error aligned pc
  refine ⟨fuel, t, executed, post, ?_⟩
  by_cases exhausted : UintCodec.Body.needsAllocation width data ∧ reservation s width data = none
  · simp only [exhausted, ↓reduceIte]
    have observed := post.body.observed
    simpa [UintCodec.Body.Observation, exhausted.1, owned.reservation, exhausted.2,
      UintCodec.Allocated.Observation] using observed
  · simp only [exhausted, ↓reduceIte]
    have resources : UintCodec.Body.needsAllocation width data →
        (UintCodec.Allocated.reservation (entered s .uint) (count data)).isSome := by
      intro needs
      cases allocated : UintCodec.Allocated.reservation (entered s .uint) (count data) with
      | none =>
        apply False.elim
        apply exhausted
        refine ⟨needs, ?_⟩
        rw [← owned.reservation]
        simpa only [UintCodec.Body.reservation, needs, ↓reduceIte, count] using allocated
      | some q => rfl
    simpa only [entered_reg _ _ 0#5 (by decide) (by decide) (by decide)] using post.body.refines resources

end SszArm.Dispatch.Unsigned

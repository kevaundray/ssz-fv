import SszArm.BitVectorBody

namespace SszArm.BitVector

/-- All-path native refinement: real postdispatch entry, linked arithmetic and
memcpy helpers, every body branch, and the common saved-activation RET. -/
theorem program_correct (s : ArmState) (base : BitVec 64)
    (length : SszNative.NatOperand) (data : Ssz.Bytes)
    (owned : Owned s length data) (code : JointCodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 428#64) :
    ∃ fuel, Post s (run fuel s) length data := by
  obtain ⟨bodyFuel, final, execution, completed⟩ :=
    body_correct s base length data owned code error aligned pc
  refine ⟨bodyFuel + 8, ?_⟩
  rw [run_plus, execution]
  exact completed.post owned aligned

/-- Scratch exhaustion remains an explicit host failure. Every other execution
returns the pinned SSZ BitVector result while satisfying the full physical
scratch, readonly-byte, caller-activation, and zero-copy postcondition. -/
theorem program_refines (s : ArmState) (base : BitVec 64)
    (length : SszNative.NatOperand) (data : Ssz.Bytes)
    (owned : Owned s length data) (code : JointCodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 428#64) :
    ∃ fuel, Post s (run fuel s) length data ∧
      (SszNative.BitVector.Exhausted length (arenaOf s) →
        SszNative.BitVector.failureAt (UintCodec.widthLoad (run fuel s))
          (r (.GPR 0#5) s).toNat .scratchExhausted) ∧
      (¬ SszNative.BitVector.Exhausted length (arenaOf s) →
        SszNative.BitView.ResultAt (UintCodec.widthLoad (run fuel s))
          (r (.GPR 0#5) s).toNat (Ssz.deserialize (.bitVector length.value) data)) := by
  obtain ⟨fuel, post⟩ := program_correct s base length data owned code error aligned pc
  exact ⟨fuel, post, Post.refines owned post⟩

end SszArm.BitVector

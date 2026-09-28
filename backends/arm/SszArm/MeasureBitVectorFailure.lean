import SszArm.MeasureBitVectorFacts
import SszArm.MeasureBitsScratchFields
import SszArm.MeasureErrorWritersProduced

namespace SszArm.Measure.BitVector

open SszNative (NatOperand)
open SszNative.Serialize (Packed)

theorem failed_outcome (s : ArmState) (args : Args) (cap : NatOperand) (bits : Packed)
    (mismatch : cap.value ≠ bits.count.toNat)
    (failed : (SszNative.NatArithmetic.fromWide (arenaOf s args).base (arenaOf s args).capacity
      (arenaOf s args).used bits.count).result = .error .scratchExhausted) :
    outcome s args (.bitVector cap) (.bits bits) =
      ⟨.error (.arithmetic .scratchExhausted), (arenaOf s args).used,
        [SszNative.NatArithmetic.unchanged (arenaOf s args).used (.error .scratchExhausted)]⟩ := by
  by_cases small : bits.count.toNat < 2^64
  · simp [SszNative.NatArithmetic.fromWide, small, SszNative.NatArithmetic.unchanged] at failed
  · cases reserve : SszNative.Arena.reserve (arenaOf s args).base (arenaOf s args).capacity
      (arenaOf s args).used 2 with
    | none =>
      simp [outcome, SszNative.Serialize.measure, mismatch, SszNative.Serialize.fromWide,
        SszNative.Serialize.bind, SszNative.Serialize.unchanged, SszNative.NatArithmetic.fromWide,
        small, reserve, SszNative.NatArithmetic.unchanged, Except.mapError]
    | some reservation =>
      simp [SszNative.NatArithmetic.fromWide, small, reserve,
        SszNative.NatArithmetic.committed] at failed

theorem scratch_body (s : ArmState) (base : BitVec 64) (args : Args)
    (cap : NatOperand) (bits : Packed)
    (owned : Owned s args (.bitVector cap) (.bits bits))
    (output : r (.GPR 19#5) s = args.result) (stack : r (.GPR 31#5) s = args.bodySP)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3528#64) (mismatch : cap.value ≠ bits.count.toNat)
    (failed : (SszNative.NatArithmetic.fromWide (arenaOf s args).base (arenaOf s args).capacity
      (arenaOf s args).used bits.count).result = .error .scratchExhausted) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args (.bitVector cap) (.bits bits) base := by
  have measured := failed_outcome s args cap bits mismatch failed
  have failure : (outcome s args (.bitVector cap) (.bits bits)).result =
      .error (.arithmetic .scratchExhausted) := by rw [measured]
  have unallocated : ∀ call ∈ (outcome s args (.bitVector cap) (.bits bits)).calls,
      call.allocation = none := by
    intro call member
    have equal : call = SszNative.NatArithmetic.unchanged (arenaOf s args).used
        (.error .scratchExhausted) := by simpa only [measured, List.mem_singleton] using member
    subst call
    rfl
  have noWrites := allocationWrites_of_unallocated args (outcome s args (.bitVector cap) (.bits bits))
    unallocated
  have writes : Result.errorWrites s = bodyWrites args (outcome s args (.bitVector cap) (.bits bits)) := by
    simpa only [bodyWrites, noWrites, List.append_nil] using
      local_error_writes owned.stackLow output stack mismatch _ failure
  have space := Result.semantic_error_space owned output stack _ failure
    (mismatch_inline s args cap bits mismatch)
  refine ⟨51, Bits.Scratch.finalResult s base, Bits.Scratch.executes s base code error aligned pc, ?_⟩
  apply Produced.of_unallocated owned unallocated (by rw [measured])
    (Bits.Scratch.final_pc s base) (Bits.Scratch.final_program s base)
    ((Bits.Scratch.final_error s base).trans error) ((Bits.Scratch.final_sp s base).trans stack)
  · simpa only [failure, output] using Bits.Scratch.final_at s base space
  · simpa only [writes] using Bits.Scratch.final_frame s base space
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      exact Bits.Scratch.final_register s base _ (by decide) (by decide) (by decide)
  · intro reg low high
    rw [Bits.Scratch.final_vector]

end SszArm.Measure.BitVector

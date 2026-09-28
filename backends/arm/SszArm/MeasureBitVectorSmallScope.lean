import SszArm.MeasureBitVectorFacts
import SszArm.MeasureBitVectorScopeFields
import SszArm.MeasureErrorWritersProduced

namespace SszArm.Measure.BitVector

open SszNative (NatOperand)
open SszNative.Serialize (Packed)

theorem small_scope_body (s : ArmState) (base : BitVec 64) (args : Args)
    (cap : NatOperand) (bits : Packed)
    (owned : Owned s args (.bitVector cap) (.bits bits))
    (output : r (.GPR 19#5) s = args.result) (stack : r (.GPR 31#5) s = args.bodySP)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 3416#64) (descriptor : r (.GPR 1#5) s = args.descriptor + 8#64)
    (pointer : r (.GPR 10#5) s = 0#64) (payload : r (.GPR 8#5) s = bits.count.setWidth 64)
    (mismatch : cap.value ≠ bits.count.toNat) (small : bits.count.toNat < 2^64) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args (.bitVector cap) (.bits bits) base := by
  have measured := small_outcome s args cap bits mismatch small
  have failure : (outcome s args (.bitVector cap) (.bits bits)).result =
      .error (.scope cap (.small (bits.count.setWidth 64))) := by rw [measured]
  have unallocated : ∀ call ∈ (outcome s args (.bitVector cap) (.bits bits)).calls,
      call.allocation = none := by
    intro call member
    have equal : call = SszNative.NatArithmetic.unchanged (arenaOf s args).used
        (.ok (.small (bits.count.setWidth 64))) := by
      simpa only [measured, List.mem_singleton] using member
    subst call
    rfl
  have noWrites := allocationWrites_of_unallocated args (outcome s args (.bitVector cap) (.bits bits))
    unallocated
  have writes : Result.errorWrites s = bodyWrites args (outcome s args (.bitVector cap) (.bits bits)) := by
    simpa only [bodyWrites, noWrites, List.append_nil] using
      local_error_writes owned.stackLow output stack mismatch _ failure
  have space := Result.semantic_error_space owned output stack _ failure
    (mismatch_inline s args cap bits mismatch)
  have borrowed : NatDivision.OperandOwned (Result.errorWrites s) cap :=
    operand_owned_subset cap
      (owned.operandOwned cap (by simp [Emit.descriptorOperands, Emit.valueOperands])) (by
        intro span member
        apply bodyWrites_subset args (outcome s args (.bitVector cap) (.bits bits)) span
        simpa only [writes] using member)
  obtain ⟨expectedPointer, expectedPayload⟩ := cap_reads owned
  have result := Scope.result_at s base space cap (.small (bits.count.setWidth 64))
    (by simpa only [descriptor] using expectedPointer)
    (by simpa [descriptor, BitVec.add_assoc] using expectedPayload)
    (by simpa only [NatOperand.pointer] using pointer)
    (by simpa only [NatOperand.payload] using payload)
    (owned.operand_at cap (by simp [Emit.descriptorOperands, Emit.valueOperands]))
    (by trivial) borrowed (by trivial)
  refine ⟨30, Scope.result s base, Scope.executes s base code error aligned pc, ?_⟩
  apply Produced.of_unallocated owned unallocated (by rw [measured])
    (Scope.result_pc s base) (Scope.result_program s base)
    ((Scope.result_error s base).trans error) ((Scope.result_sp s base).trans stack)
  · simpa only [failure, output] using result
  · simpa only [writes] using Scope.result_frame s base space
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      exact Scope.result_register s base _ (by decide) (by decide) (by decide) (by decide)
  · intro reg low high
    rw [Scope.result_vector]

end SszArm.Measure.BitVector

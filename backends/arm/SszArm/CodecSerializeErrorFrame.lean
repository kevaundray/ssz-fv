import SszArm.CodecSerializeOutputFrame
import SszArm.CodecSerializeRestore
import SszArm.CodecSerializeProvenance

namespace SszArm.Codec.Serialize

open SszNative.Codec (Desc Value)

 theorem result_local_covered (args : Args) (desc : Desc) :
    BitVector.Covers (stackSpans args desc ++ externalSpans args)
      (stackSpans args desc ++ [(args.result.toNat, 72)]) := by
  intro span member
  rcases List.mem_append.mp member with stack | result
  · exact ⟨span, List.mem_append.mpr (Or.inl stack), Nat.le_refl _, Nat.le_refl _⟩
  · simp only [List.mem_singleton] at result
    subst span
    exact ⟨(args.result.toNat, 72), by simp [externalSpans], Nat.le_refl _, Nat.le_refl _⟩

 theorem noOutput_envelope_covered (s : ArmState) (args : Args) (desc : Desc) :
    BitVector.Covers (envelope s args desc) (noOutputEnvelope s args desc) := by
  intro span member
  rcases List.mem_append.mp member with localMember | arena
  · obtain ⟨outer, included, lower, upper⟩ := result_local_covered args desc span localMember
    exact ⟨outer, List.mem_append.mpr (Or.inl included), lower, upper⟩
  · exact ⟨span, List.mem_append.mpr (Or.inr arena), Nat.le_refl _, Nat.le_refl _⟩

 theorem error_copy_local_covered (t : ArmState) (args : Args) (desc : Desc)
    (registers : SszArm.Serialize.Registers t args) (low : requiredStack desc ≤ args.stack.toNat) :
    BitVector.Covers (stackSpans args desc ++ [(args.result.toNat, 72)])
      (SszArm.Serialize.Finish.measureWrites t) := by
  have minimum := requiredStack_min desc
  have stackAddress := SszArm.Serialize.bodySP_toNat args (by omega)
  change BitVector.Covers _
    [((r (.GPR 31#5) t).toNat + 8, 16), ((r (.GPR 19#5) t).toNat, 72)]
  rw [registers.stack, registers.result]
  intro span member
  simp only [List.mem_cons, List.mem_singleton] at member
  rcases member with rfl | rfl
  · refine ⟨(args.stack.toNat - requiredStack desc, requiredStack desc),
      by simp [stackSpans, Stack.envelope], ?_, ?_⟩ <;> dsimp <;> rw [stackAddress] <;> omega
  · exact ⟨(args.result.toNat, 72), by simp, Nat.le_refl _, Nat.le_refl _⟩

 theorem error_copy_covered (t : ArmState) (args : Args) (desc : Desc)
    (registers : SszArm.Serialize.Registers t args) (low : requiredStack desc ≤ args.stack.toNat) :
    BitVector.Covers (stackSpans args desc ++ externalSpans args)
      (SszArm.Serialize.Finish.measureWrites t) :=
  (result_local_covered args desc).trans (error_copy_local_covered t args desc registers low)

 theorem error_copy_noOutput_covered (s t : ArmState) (args : Args) (desc : Desc)
    (registers : SszArm.Serialize.Registers t args) (low : requiredStack desc ≤ args.stack.toNat) :
    BitVector.Covers (noOutputEnvelope s args desc) (SszArm.Serialize.Finish.measureWrites t) := by
  intro span member
  obtain ⟨outer, included, lower, upper⟩ := error_copy_local_covered t args desc registers low span member
  exact ⟨outer, List.mem_append.mpr (Or.inl included), lower, upper⟩

end SszArm.Codec.Serialize

import SszArm.DispatchBitVectorEntry

namespace SszArm.Dispatch.BitVector

open Delimited (Protected)
open SszArm.BitVector (Covers)

theorem entered_activation {s : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) :
    (r (.GPR 31#5) (entered s .bitVector)).toNat + 272 = (savedSpan s).1 := by
  have low := owned.stackLow
  rw [entered_sp, bodySP_nat owned]
  simp only [savedSpan]
  omega

theorem local_covered (s : ArmState) : Covers (localWrites s ++ [savedSpan s]) (localWrites s) := by
  intro span member
  exact ⟨span, List.mem_append_left _ member, Nat.le_refl _, Nat.le_refl _⟩

/-- Every accepted body obligation is derived from the original physical ABI,
including the complete operand allocation, fresh suffix, nested call frame and
saved activation. This lemma is not a public theorem premise. -/
theorem body_owned {s : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) : SszArm.BitVector.Owned (entered s .bitVector) length data := by
  have low := owned.stackLow
  have sp := bodySP_nat owned
  have reg0 := entered_reg s .bitVector 0#5 (by decide) (by decide) (by decide)
  have reg1 := entered_reg s .bitVector 1#5 (by decide) (by decide) (by decide)
  have reg2 := entered_reg s .bitVector 2#5 (by decide) (by decide) (by decide)
  have reg3 := entered_reg s .bitVector 3#5 (by decide) (by decide) (by decide)
  refine {
    length := by rw [reg3]; exact owned.length
    inputBound := by rw [reg2]; exact owned.inputBound
    input := by rw [reg2]; exact entered_input owned
    descriptorBound := by rw [reg1]; exact owned.descriptorBound
    descriptor := by rw [reg1]; exact entered_descriptor owned
    outputBound := by rw [reg0]; exact owned.outputBound
    stackLow := by rw [entered_sp, sp]; omega
    stackHigh := by rw [entered_sp, sp]; have upper := (r (.GPR 31#5) s).isLt; omega
    outputStack := ?_
    arenaBound := by rw [entered_arena]; exact owned.arenaBound
    arenaStorage := by rw [entered_arenaOf owned]; exact owned.arenaStorage
    arenaUsed := by rw [entered_arenaOf owned]; exact owned.arenaUsed
    arenaNonnull := by rw [entered_arenaOf owned]; exact owned.arenaNonnull
    arenaLocal := ?_
    availableLocal := ?_
    availableInput := by rw [entered_available owned, reg2]; exact owned.availableInput
    availableDescriptor := by rw [entered_available owned, reg1]; exact owned.availableDescriptor
    availableOperand := by rw [entered_available owned]; exact owned.availableOperand
    fresh := ?_
    inputOwned := ?_
    descriptorOwned := ?_
    operandOwned := ?_
    activationOwned := ?_ }
  · rw [entered_sp, sp, reg0]
    simpa only [Nat.sub_sub] using owned.outputStack
  · rw [entered_locals owned, entered_arena]
    exact (local_covered s).protected owned.arenaLocal
  · rw [entered_locals owned, entered_activation owned, entered_arena, entered_available owned]
    exact owned.availableLocal
  · intro span member
    rw [entered_outcome owned] at member
    rw [entered_locals owned, entered_activation owned, entered_arena]
    exact owned.fresh span member
  · rw [entered_bodyWrites owned, reg2]
    exact (body_covered s (outcome s length data)).protected owned.inputOwned
  · rw [entered_bodyWrites owned, reg1]
    exact (body_covered s (outcome s length data)).protected owned.descriptorOwned
  · rw [entered_bodyWrites owned]
    exact (body_covered s (outcome s length data)).operand length owned.operandOwned
  · rw [entered_bodyWrites owned, entered_activation owned]
    exact owned.activationOwned

end SszArm.Dispatch.BitVector

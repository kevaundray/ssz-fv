import SszX86.CodecSerializeInputs

namespace SszX86.CodecSerialize
open SszNative UintCodec

/-- The original five PUSHes and CALL42 establish the complete recursive measure
contract. This derivation neither predicts a branch nor assumes a callee run. -/
theorem Owned.measure_owned {s : MachineData} {base : Int64}
    {desc : SszNative.Codec.Desc} {value : SszNative.Codec.Value} {readonly : Codec.Footprint}
    {address capacity used ra : BitVec 64}
    (owned : Owned s base desc value readonly address capacity used ra) :
    CodecMeasure.Owned (Serialize.measureState s base) (base + Int64.ofInt measureOffset)
      desc value readonly address capacity used (base + 47).toBitVec true := by
  have low := owned.stack.lowEnough
  have low144 := stackBytes_wrapper desc
  have high := owned.returnBound
  have stackNat := owned.measure_stack_nat
  have planNat : (Serialize.measureState s base).regs.rdi.toNat = s.regs.rsp.toNat - 112 := by
    rw [← UInt64.toNat_toBitVec, Serialize.measureState_plan_pointer]
    exact owned.plan_pointer_nat
  have bottomNat : (Serialize.measureState s base).regs.rsp.toNat - CodecMeasure.stackBytes desc =
      s.regs.rsp.toNat - stackBytes desc := by
    unfold stackBytes
    omega
  have planMapped := owned.stack_window_mapped 112 72 (by decide) (by omega)
  have childStack := owned.stack.substack 144 (CodecMeasure.stackBytes desc) (Nat.le_refl _)
  refine {
    physical := owned.physical
    descriptor := owned.measure_descriptor
    valueStored := owned.measure_value
    descriptorMapped := Serialize.measureState_extension s base _ _ owned.descriptorMapped
    valueMapped := Serialize.measureState_extension s base _ _ owned.valueMapped
    retainFlag := by
      change (1 : UInt64).toBitVec.setWidth 8 = BitVec.ofNat 8 1
      decide
    arena := owned.measure_arena
    usedBound := owned.usedBound
    arenaBound := owned.arenaBound
    arenaNonzero := owned.arenaNonzero
    arenaMapped := Serialize.measureState_extension s base _ _ owned.arenaMapped
    resultBound := by omega
    resultAligned := by have := owned.stackAligned; omega
    resultNonzero := by omega
    resultMapped := ?_
    headerBound := owned.headerBound
    stack := ?_
    stackAligned := by have := owned.stackAligned; omega
    returnBound := by omega
    returnSlot := Serialize.measureState_return_load s base
    resultHeader := ?_
    resultStack := ?_
    headerStack := ?_
    freeResult := ?_
    freeHeader := owned.freeHeader
    freeStack := ?_
    readonlyDisjoint := ?_
    table := owned.measure_table
    tableReadonly := owned.measureTableReadonly
    classifierTable := owned.measure_classifier_table
    classifierTableReadonly := owned.classifierTableReadonly }
  · rw [Serialize.measureState_plan_pointer]
    exact Serialize.measureState_extension s base _ _ planMapped
  · rw [Serialize.measureState_stack_pointer]
    exact ⟨childStack.lowEnough, Serialize.measureState_extension s base _ _ childStack.mapped⟩
  · simp only [Serialize.measureState_plan_pointer, Serialize.measureState_arena_pointer]
    intro i hi j hj equal
    apply owned.headerStack j hj (stackBytes desc - 112 + i) (by omega)
    have pointer : Serialize.planPointer s + BitVec.ofNat 64 i =
        stackBase s desc + BitVec.ofNat 64 (stackBytes desc - 112 + i) := by
      unfold Serialize.planPointer stackBase
      bv_omega
    exact equal.symm.trans pointer
  · rw [Serialize.measureState_plan_pointer, measure_bottom]
    intro i hi j hj
    unfold Serialize.planPointer stackBase stackBytes
    simp only [← UInt64.toNat_toBitVec] at low high
    unfold stackBytes at low
    bv_omega
  · rw [Serialize.measureState_arena_pointer, measure_bottom]
    intro i hi j hj
    exact owned.headerStack i hi j (by unfold stackBytes; omega)
  · rw [planNat]
    have apart := owned.freeStack
    unfold Body.Apart at apart ⊢
    omega
  · rw [bottomNat]
    have apart := owned.freeStack
    unfold Body.Apart at apart ⊢
    unfold stackBytes at apart
    omega
  · intro a borrowed writes
    exact owned.readonlyDisjoint a borrowed (measure_available s base desc address capacity used a writes)

end SszX86.CodecSerialize

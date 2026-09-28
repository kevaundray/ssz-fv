import SszX86.MeasureEntryState

namespace SszX86.Measure
open SszNative SszNative.Serialize UintCodec

theorem Owned.at_body {s t : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64} {retain : Bool}
    (owned : Owned s base desc value buffer address capacity used ra retain)
    (anchors : AtBody s t)
    (tag : t.regs.rax.toBitVec.setWidth 8 = BitVec.ofNat 8 (valueTag value)) :
    BodyOwned t desc value buffer address capacity used := by
  have stackLow := owned.stackLow
  have returnBound := owned.returnBound
  have localPointer : t.regs.rsp.toBitVec - 16 = s.regs.rsp.toBitVec - 280 := by
    rw [anchors.stack]
    bv_omega
  have stackNat : t.regs.rsp.toNat = s.regs.rsp.toNat - 264 := by
    have sp := anchors.stack
    simp only [← UInt64.toNat_toBitVec] at stackLow ⊢
    bv_omega
  have localNat : t.regs.rsp.toNat - 16 = s.regs.rsp.toNat - 280 := by omega
  have localMap : Large.Mapped (savedMem s) (s.regs.rsp.toBitVec - 280) 232 := by
    have hm := Dispatch.saved_mapped s _ _ owned.stackMapped
    intro i hi
    exact hm i (by omega)
  refine {
    physical := owned.physical
    descriptor := ?_
    descriptorMapped := ?_
    valueStored := ?_
    tag := tag
    arena := ?_
    descriptorBound := ?_
    valueBound := ?_
    resultBound := ?_
    headerBound := ?_
    stackLow := by omega
    stackBound := by omega
    arenaBound := owned.arenaBound
    arenaNonzero := owned.arenaNonzero
    resultMapped := ?_
    localMapped := ?_
    freeMapped := ?_
    resultHeader := ?_
    resultStack := ?_
    headerStack := ?_
    freeResult := ?_
    freeHeader := ?_
    freeStack := ?_
    readonly := ?_ }
  · simpa only [anchors.memory, anchors.descriptorPointer] using owned.saved_descriptor
  · simpa only [anchors.memory, anchors.descriptorPointer] using
      Dispatch.saved_mapped s _ _ owned.descriptorMapped
  · simpa only [anchors.memory, anchors.valuePointer] using owned.saved_value
  · simpa only [anchors.memory, anchors.arenaPointer] using owned.saved_header
  · simpa only [anchors.descriptorPointer] using owned.descriptorBound
  · simpa only [anchors.valuePointer] using owned.valueBound
  · simpa only [anchors.result] using owned.resultBound
  · simpa only [anchors.arenaPointer] using owned.headerBound
  · simpa only [anchors.memory, anchors.result] using Dispatch.saved_mapped s _ _ owned.resultMapped
  · simpa only [anchors.memory, localPointer] using localMap
  · simpa only [anchors.memory] using Dispatch.saved_mapped s _ _ owned.freeMapped
  · simpa only [anchors.result, anchors.arenaPointer] using owned.resultHeader
  · simpa only [anchors.result, localPointer] using owned.resultStack
  · simpa only [anchors.arenaPointer, localPointer] using owned.headerStack
  · simpa only [anchors.result] using owned.freeResult
  · simpa only [anchors.arenaPointer] using owned.freeHeader
  · simpa only [localNat] using owned.freeStack
  · intro a borrowed writable
    have original : Borrowed s desc value buffer a := by
      simpa only [BodyBorrowed, Borrowed, anchors.descriptorPointer, anchors.valuePointer] using borrowed
    apply owned.readonly a original
    simp only [anchors.result, anchors.arenaPointer, localPointer] at writable
    rcases writable with result | header | arena | ⟨i, hi, equal⟩
    · exact Or.inl result
    · exact Or.inr (Or.inl header)
    · exact Or.inr (Or.inr (Or.inl arena))
    · exact Or.inr (Or.inr (Or.inr ⟨i, by omega, equal⟩))

end SszX86.Measure

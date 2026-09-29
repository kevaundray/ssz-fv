import SszX86.CodecEmitInvariant
import SszX86.CodecStorage

set_option autoImplicit false

namespace SszX86.CodecEmit
open SszNative UintCodec

/-- Physical resources for invoking the immutable primitive provider inside a
recursive activation. Its historical 80-byte result exclusion is explicit here;
no bytes in the extra exclusion, or in result padding, must be initialized. -/
structure PrimitiveMemory (s : MachineData) (base : Int64)
    (shape : Serialize.Desc) (value : SszNative.Codec.Value)
    (r : SszX86.Codec.Footprint) (ra : BitVec 64) (written : Nat) : Prop where
  physical : value.Physical
  descriptor : SszX86.Codec.DescAt s.dmem r s.regs.rsi.toBitVec (.primitive shape)
  valueStored : SszX86.Codec.ValueAt s.dmem r s.regs.rdx.toBitVec value
  outputBound : s.regs.r8.toNat + s.regs.r9.toNat ≤ 2 ^ 64
  resultExclusionBound : s.regs.rdi.toNat + 80 ≤ 2 ^ 64
  stackLow : 160 ≤ s.regs.rsp.toNat
  returnBound : s.regs.rsp.toNat + 8 ≤ 2 ^ 64
  outputMapped : Large.Mapped s.dmem s.regs.r8.toBitVec written
  lengthMapped : Large.Mapped s.dmem s.regs.rdi.toBitVec 8
  statusMapped : Large.Mapped s.dmem (s.regs.rdi.toBitVec + 64) 4
  stackMapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 160) 160
  returnSlot : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))
  outputResult : Large.Disjoint s.regs.r8.toBitVec s.regs.rdi.toBitVec written 80
  outputStack : Large.Disjoint s.regs.r8.toBitVec (s.regs.rsp.toBitVec - 160) written 168
  resultStack : Large.Disjoint s.regs.rdi.toBitVec (s.regs.rsp.toBitVec - 160) 80 168
  tailReadonly : ∀ i, written ≤ i → i < s.regs.r9.toNat →
    ¬ (Emit.InSpan (s.regs.r8.toBitVec + BitVec.ofNat 64 i) s.regs.rdi.toBitVec 8 ∨
      Emit.InSpan (s.regs.r8.toBitVec + BitVec.ofNat 64 i) (s.regs.rdi.toBitVec + 64) 4 ∨
      Emit.InSpan (s.regs.r8.toBitVec + BitVec.ofNat 64 i) (s.regs.rsp.toBitVec - 160) 160)
  readonly : ∀ a, r a → ¬ Emit.Writable s written a
  table : Emit.TableAt s.dmem base
  tableReadonly : ∀ a, Emit.InSpan a (Emit.tableAddress base) 16 →
    ¬ Emit.Writable s written a

private theorem primitive_value {m : DataMem} {r : SszX86.Codec.Footprint}
    {p : BitVec 64} {value : SszNative.Codec.Value} {shape : Serialize.Desc}
    (stored : SszX86.Codec.ValueAt m r p value)
    (compatible : Emit.Compatible shape value.toPrimitive) :
    ∃ buffer, SszX86.Codec.PrimitiveValueAt m r p buffer value.toPrimitive := by
  cases stored with
  | valueBool h | valueUint h | valueBytes h | valueBits h => exact ⟨_, h⟩
  | valueSeq h children values =>
    cases shape <;> simp [SszNative.Codec.Value.toPrimitive, Emit.Compatible] at compatible
  | valueUnion h selector pointer child =>
    cases shape <;> simp [SszNative.Codec.Value.toPrimitive, Emit.Compatible] at compatible

/-- The old provider's complete primitive ownership is derived from recursive
storage and the generated call; no tag-only storage relation is substituted. -/
theorem PrimitiveMemory.owned {s : MachineData} {base : Int64}
    {shape : Serialize.Desc} {value : SszNative.Codec.Value}
    {supplied : Option SszNative.CodecMeasure.Plan} {r : SszX86.Codec.Footprint}
    {ra : BitVec 64} (call : GeneratedCall (.primitive shape) value supplied s.regs.r9.toNat)
    (memory : PrimitiveMemory s base shape value r ra call.measured.size.value) :
    ∃ buffer, Emit.Owned s base shape value.toPrimitive buffer ra call.measured.size.value := by
  have valid := call.primitive_valid
  obtain ⟨buffer, stored⟩ := primitive_value memory.valueStored
    (Emit.success_compatible shape value.toPrimitive _ valid.success)
  have descSize : Emit.descBytes shape ≤ 40 := by cases shape <;> decide
  have valueSize : Emit.valueBytes value.toPrimitive ≤ 48 := by cases value <;> decide
  have descriptor : SszX86.Codec.PrimitiveDescAt s.dmem r s.regs.rsi.toBitVec shape := by
    cases memory.descriptor with
    | descPrimitive h => exact h
  have descBound := descriptor.span.bound
  have valueBound := stored.span.bound
  refine ⟨buffer, {
    valid := valid
    physical := value.physical_toPrimitive memory.physical
    descriptor := descriptor.stored
    valueStored := stored.stored
    descriptorBound := ?_
    valueBound := ?_
    outputBound := memory.outputBound
    resultBound := memory.resultExclusionBound
    stackLow := memory.stackLow
    returnBound := memory.returnBound
    outputMapped := memory.outputMapped
    lengthMapped := memory.lengthMapped
    statusMapped := memory.statusMapped
    stackMapped := memory.stackMapped
    returnSlot := memory.returnSlot
    outputResult := memory.outputResult
    outputStack := memory.outputStack
    resultStack := memory.resultStack
    tailReadonly := memory.tailReadonly
    readonly := ?_
    table := memory.table
    tableReadonly := memory.tableReadonly }⟩
  · simpa only [UInt64.toNat_toBitVec] using (by omega :
      s.regs.rsi.toBitVec.toNat + Emit.descBytes shape ≤ 2 ^ 64)
  · simpa only [UInt64.toNat_toBitVec] using (by omega :
      s.regs.rdx.toBitVec.toNat + Emit.valueBytes value.toPrimitive ≤ 2 ^ 64)
  · intro a borrowed
    apply memory.readonly a
    rcases borrowed with desc | val | descBorrow | valBorrow
    · obtain ⟨i, hi, same⟩ := desc
      exact descriptor.span.covered a ⟨i, by omega, same⟩
    · obtain ⟨i, hi, same⟩ := val
      exact stored.span.covered a ⟨i, by omega, same⟩
    · exact descriptor.borrowed a descBorrow
    · exact stored.borrowed a valBorrow

end SszX86.CodecEmit

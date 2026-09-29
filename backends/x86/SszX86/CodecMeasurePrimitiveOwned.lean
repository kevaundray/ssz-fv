import SszX86.CodecMeasureOwned
import SszX86.CodecStorageAdapters

set_option autoImplicit false

namespace SszX86.CodecMeasure
open SszNative UintCodec

private theorem descriptor_live {m : DataMem} {r : Codec.Footprint} {p : BitVec 64}
    {desc : Serialize.Desc} (stored : Codec.PrimitiveDescAt m r p desc) :
    ∀ a, Measure.DescLive p desc a → r a := by
  intro a live
  rcases live with tag | payload
  · obtain ⟨i, hi, equal⟩ := tag
    exact stored.span.covered a ⟨i, by omega, equal⟩
  · cases desc with
    | bool => exact False.elim payload
    | uint _ | byteVector _ | byteList _ | bitVector _ | bitList _ =>
      exact stored.span.covered a (Emit.span_shift p 8 16 40 (by decide) payload)
    | progressiveBitList limit =>
      cases limit with
      | none => exact stored.span.covered a (Emit.span_shift p 8 4 40 (by decide) payload)
      | some operand =>
        rcases payload with tag | operand
        · exact stored.span.covered a (Emit.span_shift p 8 4 40 (by decide) tag)
        · exact stored.span.covered a (Emit.span_shift p 16 16 40 (by decide) operand)

private theorem value_live {m : DataMem} {r : Codec.Footprint} {p buffer : BitVec 64}
    {value : Serialize.Value} (stored : Codec.PrimitiveValueAt m r p buffer value) :
    ∀ a, Measure.ValueLive p value a → r a := by
  intro a live
  rcases live with tag | payload
  · obtain ⟨i, hi, equal⟩ := tag
    exact stored.span.covered a ⟨i, by omega, equal⟩
  · cases value with
    | bool _ => exact stored.span.covered a (Emit.span_shift p 1 1 48 (by decide) payload)
    | uint _ | bytes _ => exact stored.span.covered a (Emit.span_shift p 8 16 48 (by decide) payload)
    | bits _ => exact stored.span.covered a (Emit.span_shift p 16 32 48 (by decide) payload)
    | seq _ | union _ _ => exact False.elim payload

theorem stackBytes_leaf (desc : SszNative.Codec.Desc) : 280 ≤ stackBytes desc := by
  unfold stackBytes Codec.descriptorStackBytes
  exact Codec.recursiveStackBytes_helper _ _

private theorem tableAddress_primitive (base : Int64) :
    Measure.tableAddress base = tableAddress base := by
  change base.toBitVec - 89316 = base.toBitVec + BitVec.ofInt 64 (-89316)
  bv_omega

/-- The legacy seven-leaf precondition is derived from the full recursive
ownership contract, including an empty free arena. No second input convention
or primitive-only premise is exposed by the recursive public interface. -/
theorem Owned.primitive {s : MachineData} {base : Int64} {shape : Serialize.Desc}
    {value : SszNative.Codec.Value} {readonly : Codec.Footprint}
    {address capacity used ra : BitVec 64} {retain : Bool}
    (owned : Owned s base (.primitive shape) value readonly address capacity used ra retain) :
    ∃ buffer, Measure.Owned s base shape value.toPrimitive
      buffer address capacity used ra retain := by
  obtain ⟨buffer, valueStored⟩ := owned.valueStored.toPrimitive
  have descriptor : Codec.PrimitiveDescAt s.dmem readonly s.regs.rsi.toBitVec shape := by
    cases h : owned.descriptor with
    | descPrimitive descriptor => exact descriptor
  have enough := stackBytes_leaf (.primitive shape)
  have low := owned.stack.lowEnough
  change stackBytes (.primitive shape) ≤ s.regs.rsp.toNat at low
  have usedBound := owned.usedBound
  have nested := owned.stack.substack 0 280 (by omega)
  have oldBorrowed : ∀ a, Measure.Borrowed s shape value.toPrimitive buffer a → readonly a := by
    intro a borrowed
    rcases borrowed with live | live | borrowed | borrowed
    · exact descriptor_live descriptor a live
    · exact value_live valueStored a live
    · exact descriptor.borrowed a borrowed
    · exact valueStored.borrowed a borrowed
  have stackInside : ∀ a, Emit.InSpan a (s.regs.rsp.toBitVec - 280) 280 →
      Codec.StackWrites s.regs.rsp.toBitVec (stackBytes (.primitive shape)) a := by
    intro a inside
    simpa only [BitVec.ofNat_zero, BitVec.sub_zero] using
      Codec.stack_subspan s.regs.rsp.toBitVec 0 280 (stackBytes (.primitive shape))
        (by omega) a inside
  have shifted : (s.regs.rsp.toBitVec - BitVec.ofNat 64 (stackBytes (.primitive shape))) +
      BitVec.ofNat 64 (stackBytes (.primitive shape) - 280) = s.regs.rsp.toBitVec - 280 := by
    bv_omega
  refine ⟨buffer, {
    physical := value.physical_toPrimitive owned.physical
    descriptor := descriptor.stored
    descriptorMapped := ?_
    valueStored := valueStored.stored
    retainFlag := owned.retainFlag
    arena := owned.arena
    descriptorBound := ?_
    valueBound := ?_
    resultBound := owned.resultBound
    headerBound := owned.headerBound
    stackLow := by omega
    returnBound := owned.returnBound
    arenaBound := owned.arenaBound
    arenaNonzero := owned.arenaNonzero
    resultMapped := owned.resultMapped
    stackMapped := ?_
    freeMapped := ?_
    returnSlot := owned.returnSlot
    resultHeader := owned.resultHeader
    resultStack := ?_
    headerStack := ?_
    freeResult := owned.freeResult
    freeHeader := owned.freeHeader
    freeStack := ?_
    readonly := ?_
    table := ?_
    tableReadonly := ?_ }⟩
  · intro i hi
    have bytes : Emit.descBytes shape ≤ 40 := by cases shape <;> decide
    exact owned.descriptorMapped i (by omega)
  · have span := descriptor.span.bound
    have bytes : Emit.descBytes shape ≤ 40 := by cases shape <;> decide
    change s.regs.rsi.toNat + 40 ≤ 2 ^ 64 at span
    omega
  · have span := valueStored.span.bound
    have bytes : Emit.valueBytes value.toPrimitive ≤ 48 := by cases value <;> decide
    change s.regs.rdx.toNat + 48 ≤ 2 ^ 64 at span
    omega
  · simpa only [BitVec.ofNat_zero, BitVec.sub_zero] using nested.mapped
  · simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      Delimited.Reservation.mapped_subrange s.dmem address capacity.toNat used.toNat
        (capacity.toNat - used.toNat) owned.arenaMapped (by omega)
  · intro i hi j hj equal
    apply owned.resultStack i hi (stackBytes (.primitive shape) - 280 + j) (by omega)
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, shifted] using equal
  · intro i hi j hj equal
    apply owned.headerStack i hi (stackBytes (.primitive shape) - 280 + j) (by omega)
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, shifted] using equal
  · have separated := owned.freeStack
    unfold Body.Apart at separated ⊢
    omega
  · intro a borrowed written
    apply owned.readonlyDisjoint a (oldBorrowed a borrowed)
    rcases written with result | cursor | arena | stack
    · exact Or.inl result
    · exact Or.inr (Or.inl cursor)
    · exact Or.inr (Or.inr (Or.inl arena))
    · exact Or.inr (Or.inr (Or.inr (stackInside a stack)))
  · intro i hi
    rw [tableAddress_primitive]
    exact owned.table i hi
  · intro a table written
    apply owned.readonlyDisjoint a (owned.tableReadonly a (by
      rwa [tableAddress_primitive] at table))
    rcases written with result | cursor | arena | stack
    · exact Or.inl result
    · exact Or.inr (Or.inl cursor)
    · exact Or.inr (Or.inr (Or.inl arena))
    · exact Or.inr (Or.inr (Or.inr (stackInside a stack)))

end SszX86.CodecMeasure

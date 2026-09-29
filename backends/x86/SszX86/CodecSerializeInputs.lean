import SszX86.CodecSerializeGeometry

namespace SszX86.CodecSerialize
open SszNative UintCodec

private theorem Owned.readonly_stack {s : MachineData} {base : Int64}
    {desc : SszNative.Codec.Desc} {value : SszNative.Codec.Value} {readonly : Codec.Footprint}
    {address capacity used ra : BitVec 64}
    (owned : Owned s base desc value readonly address capacity used ra) :
    ∀ a, readonly a → ¬ Codec.StackWrites s.regs.rsp.toBitVec (stackBytes desc) a := by
  intro a borrowed inside
  exact owned.readonlyDisjoint a borrowed (Or.inr (Or.inr (Or.inr (Or.inr inside))))

theorem Owned.measure_descriptor {s : MachineData} {base : Int64}
    {desc : SszNative.Codec.Desc} {value : SszNative.Codec.Value} {readonly : Codec.Footprint}
    {address capacity used ra : BitVec 64}
    (owned : Owned s base desc value readonly address capacity used ra) :
    Codec.DescAt (Serialize.measureState s base).dmem readonly s.regs.rsi.toBitVec desc :=
  owned.descriptor.frame (measure_frame_stack s base desc) owned.readonly_stack

theorem Owned.measure_value {s : MachineData} {base : Int64}
    {desc : SszNative.Codec.Desc} {value : SszNative.Codec.Value} {readonly : Codec.Footprint}
    {address capacity used ra : BitVec 64}
    (owned : Owned s base desc value readonly address capacity used ra) :
    Codec.ValueAt (Serialize.measureState s base).dmem readonly s.regs.rdx.toBitVec value :=
  owned.valueStored.frame (measure_frame_stack s base desc) owned.readonly_stack

theorem Owned.measure_arena {s : MachineData} {base : Int64}
    {desc : SszNative.Codec.Desc} {value : SszNative.Codec.Value} {readonly : Codec.Footprint}
    {address capacity used ra : BitVec 64}
    (owned : Owned s base desc value readonly address capacity used ra) :
    Measure.ArenaAt (Serialize.measureState s base).dmem s.regs.r9.toBitVec address capacity used := by
  have fields (off : Nat) (bound : off + 8 ≤ 24) :
      widthLoad (Serialize.measureState s base).dmem (s.regs.r9.toNat + off) 8 =
        widthLoad s.dmem (s.regs.r9.toNat + off) 8 := by
    unfold widthLoad
    rw [← UInt64.toNat_toBitVec, width_address]
    congr 1
    apply Emit.frame_load s.dmem _ _ (measure_frame_stack s base desc)
    intro i hi inside
    obtain ⟨j, hj, equal⟩ := inside
    apply owned.headerStack (off + i) (by omega) j (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    exact equal
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Nat.add_zero, UInt64.toNat_toBitVec] using
      (fields 0 (by decide)).trans owned.arena.1
  · exact (fields 8 (by decide)).trans owned.arena.2.1
  · exact (fields 16 (by decide)).trans owned.arena.2.2

theorem Owned.measure_table {s : MachineData} {base : Int64}
    {desc : SszNative.Codec.Desc} {value : SszNative.Codec.Value} {readonly : Codec.Footprint}
    {address capacity used ra : BitVec 64}
    (owned : Owned s base desc value readonly address capacity used ra) :
    CodecMeasure.TableAt (Serialize.measureState s base).dmem (base + Int64.ofInt measureOffset) := by
  intro i hi
  rw [measure_frame_stack s base desc _ (owned.readonly_stack _
    (owned.measureTableReadonly _ ⟨i, by
      simpa only [CodecMeasure.tableBytes, List.length_cons, List.length_nil] using hi, rfl⟩))]
  exact owned.measureTable i hi

theorem Owned.measure_classifier_table {s : MachineData} {base : Int64}
    {desc : SszNative.Codec.Desc} {value : SszNative.Codec.Value} {readonly : Codec.Footprint}
    {address capacity used ra : BitVec 64}
    (owned : Owned s base desc value readonly address capacity used ra) :
    CodecIsFixed.TableAt (Serialize.measureState s base).dmem
      ((base + Int64.ofInt measureOffset) + Int64.ofInt CodecMeasure.isFixedOffset) := by
  intro i hi
  rw [measure_frame_stack s base desc _ (owned.readonly_stack _
    (owned.classifierTableReadonly _ ⟨i, by
      simpa only [CodecIsFixed.tableBytes, List.length_cons, List.length_nil] using hi, rfl⟩))]
  exact owned.classifierTable i hi

end SszX86.CodecSerialize

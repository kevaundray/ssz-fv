import SszX86.CodecEmitOwned
import SszX86.CodecEmitPrimitiveBinding
import SszX86.CodecStorageAdapters
import SszX86.EmitEntry

set_option autoImplicit false

namespace SszX86.CodecEmit
open SszNative UintCodec

theorem stackBytes_min (desc : SszNative.Codec.Desc) : 160 ≤ stackBytes desc := by
  unfold stackBytes SszX86.Codec.descriptorStackBytes SszX86.Codec.recursiveStackBytes
  omega

theorem tableAddress_primitive (base : Int64) : tableAddress base = Emit.tableAddress base := by
  change base.toBitVec + BitVec.ofInt 64 (-92800) = base.toBitVec - 92800#64
  bv_omega

theorem TableAt.primitive {m : DataMem} {base : Int64} (h : TableAt m base) :
    Emit.TableAt m base := by
  simpa only [TableAt, Emit.TableAt, tableBytes, Emit.tableBytes, tableAddress_primitive] using h

theorem Owned.push_mapped {s : MachineData} {base : Int64} {desc : SszNative.Codec.Desc}
    {value : SszNative.Codec.Value} {supplied : Option SszNative.CodecMeasure.Plan}
    {r : SszX86.Codec.Footprint} {ra : BitVec 64}
    (h : Owned s base desc value supplied r ra) :
    Large.Mapped s.dmem (s.regs.rsp.toBitVec - 48) 48 := by
  have mapped := (h.stack.substack 0 48 (by have := stackBytes_min desc; omega)).mapped
  simpa only [BitVec.ofNat_zero, BitVec.sub_zero, BitVec.ofNat_eq_ofNat] using mapped

theorem Owned.push_protected {s : MachineData} {base : Int64} {desc : SszNative.Codec.Desc}
    {value : SszNative.Codec.Value} {supplied : Option SszNative.CodecMeasure.Plan}
    {r : SszX86.Codec.Footprint} {ra : BitVec 64}
    (h : Owned s base desc value supplied r ra) (a : BitVec 64) (borrowed : r a) :
    ¬ Emit.InSpan a (s.regs.rsp.toBitVec - 48) 48 := by
  intro inside
  apply h.readonly a borrowed
  right; right; right
  have included := SszX86.Codec.stack_subspan s.regs.rsp.toBitVec 0 48 (stackBytes desc)
    (by have := stackBytes_min desc; omega) a
  apply included
  simpa only [SszX86.Codec.StackWrites, BitVec.ofNat_zero, BitVec.sub_zero,
    BitVec.ofNat_eq_ofNat] using inside

theorem Owned.saved_table {s : MachineData} {base : Int64} {desc : SszNative.Codec.Desc}
    {value : SszNative.Codec.Value} {supplied : Option SszNative.CodecMeasure.Plan}
    {r : SszX86.Codec.Footprint} {ra : BitVec 64}
    (h : Owned s base desc value supplied r ra) : Emit.TableAt (Emit.savedMem s) base := by
  have frame := SszX86.Codec.savedSix_frame s (stackBytes desc)
    (by have := stackBytes_min desc; omega)
  have original := h.table.primitive
  intro i hi
  rw [frame _ (by
    intro inside
    apply h.tableReadonly _ ?_ (Or.inr (Or.inr (Or.inr inside)))
    rw [tableAddress_primitive]
    exact ⟨i, by simpa only [Emit.tableBytes, List.length_cons, List.length_nil] using hi, rfl⟩)]
  exact original i hi

/-- Original entry to the genuine primitive body, using only the recursive
72-byte-result ownership contract. All setup state and dispatch facts are
conclusions of execution rather than original-state path assumptions. -/
theorem leaf_entry_correct (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (shape : Serialize.Desc) (value : SszNative.Codec.Value)
    (supplied : Option SszNative.CodecMeasure.Plan) (r : SszX86.Codec.Footprint)
    (ra : BitVec 64) (owned : Owned s base (.primitive shape) value supplied r ra) :
    Eventually (step e) (Emit.EntryPost s base shape value.toPrimitive) (s, base) := by
  have descriptorNat : (BitVec.ofNat 64 (Emit.descTag shape)).toNat = Emit.descTag shape := by
    cases shape <;> dsimp only [Emit.descTag] <;> decide
  have valueNat : (BitVec.ofNat 8 (Emit.valueTag value.toPrimitive)).toNat =
      Emit.valueTag value.toPrimitive := by
    cases value <;> dsimp only [SszNative.Codec.Value.toPrimitive, Emit.valueTag] <;> decide
  apply Emit.setup_runs e base code.primitive s (BitVec.ofNat 64 (Emit.descTag shape))
    (BitVec.ofNat 8 (Emit.valueTag value.toPrimitive)) _ owned.push_mapped
  · rw [descriptorNat]
    exact owned.descriptor.primitive.1
  · rw [valueNat]
    exact owned.valueStored.tag
  · intro i hi j hj equal
    apply owned.push_protected _ (owned.descriptor.span.covered _ ⟨i, by omega, rfl⟩)
    exact ⟨j, hj, equal⟩
  · intro i hi j hj equal
    apply owned.push_protected _ (owned.valueStored.span.covered _ ⟨i, by omega, rfl⟩)
    exact ⟨j, hj, equal⟩
  · apply Emit.dispatch_typed e base code.primitive s _ shape value.toPrimitive
    · exact Emit.prepared_atBody _ _ _
    · rfl
    · change (BitVec.ofNat 8 (Emit.valueTag value.toPrimitive)).setWidth 64 =
        BitVec.ofNat 64 (Emit.valueTag value.toPrimitive)
      cases value <;> rfl
    · exact Emit.success_compatible shape value.toPrimitive _ owned.call.primitive_valid.success
    · exact owned.saved_table

end SszX86.CodecEmit

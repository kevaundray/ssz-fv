import SszX86.CodecMeasureEntry
import SszX86.CodecStorageAdapters
import SszX86.CodecStack

set_option autoImplicit false

namespace SszX86.CodecMeasure
open SszNative UintCodec

private theorem descTag_bound (desc : SszNative.Codec.Desc) : Codec.descTag desc < 13 := by
  cases desc with
  | primitive shape => cases shape <;> decide
  | vector _ _ | list _ _ | progressiveList _ _ | container _
  | progressiveContainer _ _ | compatibleUnion _ => decide

private theorem valueTag_bound (value : SszNative.Codec.Value) :
    Emit.valueTag value.toPrimitive < 2 ^ 8 := by
  cases value <;> decide

/-- Derive the entire original prologue precondition from recursive immutable
storage and a caller-sized stack region. No descriptor validity is needed, and
no disjointness between readonly objects is required. -/
theorem entry_owned (s : MachineData) (base : Int64)
    (desc : SszNative.Codec.Desc) (value : SszNative.Codec.Value)
    (readonly : Codec.Footprint) (stackBytes : Nat)
    (descriptor : Codec.DescAt s.dmem readonly s.regs.rsi.toBitVec desc)
    (stored : Codec.ValueAt s.dmem readonly s.regs.rdx.toBitVec value)
    (stack : Codec.StackAt s.dmem s.regs.rsp.toBitVec stackBytes)
    (enough : 48 ≤ stackBytes)
    (separate : ∀ a, readonly a → ¬ Codec.StackWrites s.regs.rsp.toBitVec stackBytes a)
    (table : TableAt s.dmem base)
    (tableReadonly : ∀ a, Codec.InSpan a (tableAddress base) 52 → readonly a) :
    EntryOwned s base (Codec.descTag desc) (BitVec.ofNat 8 (Emit.valueTag value.toPrimitive)) := by
  have saves := stack.substack 0 48 (by omega)
  refine ⟨descTag_bound desc, ?_, descriptor.tag, ?_, ?_, ?_, table, ?_⟩
  · simpa only [BitVec.ofNat_zero, BitVec.sub_zero] using saves.mapped
  · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (valueTag_bound value)] using stored.tag
  · intro i hi j hj equal
    apply separate _ (descriptor.span.covered _ ⟨i, by omega, rfl⟩)
    apply Codec.stack_subspan s.regs.rsp.toBitVec 0 48 stackBytes (by omega)
    change Codec.InSpan _ (s.regs.rsp.toBitVec - 48) 48
    exact ⟨j, hj, equal⟩
  · intro i hi j hj equal
    apply separate _ (stored.span.covered _ ⟨i, by omega, rfl⟩)
    apply Codec.stack_subspan s.regs.rsp.toBitVec 0 48 stackBytes (by omega)
    change Codec.InSpan _ (s.regs.rsp.toBitVec - 48) 48
    exact ⟨j, hj, equal⟩
  · intro i hi j hj equal
    apply separate _ (tableReadonly _ ⟨i, hi, rfl⟩)
    apply Codec.stack_subspan s.regs.rsp.toBitVec 0 48 stackBytes (by omega)
    change Codec.InSpan _ (s.regs.rsp.toBitVec - 48) 48
    exact ⟨j, hj, equal⟩

/-- Original measure entry reaches the descriptor's real indirect destination
and preserves the full recursive input graphs, including readonly aliasing. -/
theorem entry_recursive (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (desc : SszNative.Codec.Desc) (value : SszNative.Codec.Value)
    (readonly : Codec.Footprint) (stackBytes : Nat)
    (descriptor : Codec.DescAt s.dmem readonly s.regs.rsi.toBitVec desc)
    (stored : Codec.ValueAt s.dmem readonly s.regs.rdx.toBitVec value)
    (stack : Codec.StackAt s.dmem s.regs.rsp.toBitVec stackBytes)
    (enough : 48 ≤ stackBytes)
    (separate : ∀ a, readonly a → ¬ Codec.StackWrites s.regs.rsp.toBitVec stackBytes a)
    (table : TableAt s.dmem base)
    (tableReadonly : ∀ a, Codec.InSpan a (tableAddress base) 52 → readonly a) :
    Eventually (step e) (fun t =>
      t.2 = base + Int64.ofNat (tableEntry (Codec.descTag desc)) ∧
      Measure.AtBody s t.1 ∧
      t.1.regs.rax.toBitVec.setWidth 8 = BitVec.ofNat 8 (Emit.valueTag value.toPrimitive) ∧
      Codec.DescAt t.1.dmem readonly s.regs.rsi.toBitVec desc ∧
      Codec.ValueAt t.1.dmem readonly s.regs.rdx.toBitVec value) (s, base) := by
  apply eventually_weaken (step e) _ _ _ _
    (entry_runs e base code s _ _
      (entry_owned s base desc value readonly stackBytes descriptor stored stack enough
        separate table tableReadonly))
  intro t post
  refine ⟨post.1, post.2.1, post.2.2, ?_, ?_⟩
  · rw [post.2.1.memory]
    exact descriptor.savedSix stackBytes enough separate
  · rw [post.2.1.memory]
    exact stored.savedSix stackBytes enough separate

end SszX86.CodecMeasure

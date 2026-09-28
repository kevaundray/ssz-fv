import SszX86.EmitRoute

namespace SszX86.Emit
open SszNative.Serialize

/-- All seven logical primitive kinds select their actual body entry. Seq and
Union table entries are excluded by successful expectedSize, not by a path premise. -/
theorem dispatch_typed (e : Executable) (base : Int64) (hc : CodeAt e base)
    (original s : MachineData) (desc : Desc) (value : Value)
    (anchors : AtBody original s)
    (descriptor : s.regs.rax.toBitVec = BitVec.ofNat 64 (descTag desc))
    (valueKind : s.regs.rcx.toBitVec = BitVec.ofNat 64 (valueTag value))
    (compatible : Compatible desc value) (table : TableAt s.dmem base) :
    Eventually (step e) (EntryPost original base desc value) (s, base + 32) := by
  cases desc <;> cases value <;> simp only [Compatible] at compatible
  · apply select_bool e base hc s _ (by simpa only [descTag] using descriptor)
    intro af
    apply Eventually.done
    exact ⟨rfl, anchors.tested af, descriptor, fun _ => valueKind⟩
  · apply select_uint e base hc s _ (by simpa only [descTag] using descriptor)
    apply Eventually.done
    exact ⟨rfl, anchors.compared, descriptor, fun _ => valueKind⟩
  · apply dispatch_table_correct e base hc original s _ _ .bytes anchors descriptor valueKind table <;>
      dsimp only [descTag, valueTag, bodyEntry, TableKind.index, TableKind.entry] <;> decide
  · apply dispatch_table_correct e base hc original s _ _ .bytes anchors descriptor valueKind table <;>
      dsimp only [descTag, valueTag, bodyEntry, TableKind.index, TableKind.entry] <;> decide
  · apply dispatch_table_correct e base hc original s _ _ .bits anchors descriptor valueKind table <;>
      dsimp only [descTag, valueTag, bodyEntry, TableKind.index, TableKind.entry] <;> decide
  · apply dispatch_table_correct e base hc original s _ _ .bits anchors descriptor valueKind table <;>
      dsimp only [descTag, valueTag, bodyEntry, TableKind.index, TableKind.entry] <;> decide
  · apply dispatch_table_correct e base hc original s _ _ .bits anchors descriptor valueKind table <;>
      dsimp only [descTag, valueTag, bodyEntry, TableKind.index, TableKind.entry] <;> decide

end SszX86.Emit

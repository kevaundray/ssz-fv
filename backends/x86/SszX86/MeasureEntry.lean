import SszX86.MeasureEntryOwned

namespace SszX86.Measure
open SszNative SszNative.Serialize

/-- Original PC0 through the actual table-indexed JMP. No body entry is assumed. -/
theorem entry_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used ra : BitVec 64) (retain : Bool)
    (owned : Owned s base desc value buffer address capacity used ra retain)
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      (entryState s base desc value, base + Int64.ofNat (bodyEntry desc))) :
    Eventually (step e) P (s, base) := by
  apply setup_runs e base hc s (BitVec.ofNat 64 (descTag desc))
    (BitVec.ofNat 8 (valueTag value)) P owned.saved_stack_mapped
  · have bound : descTag desc < 2^64 := by cases desc <;> dsimp only [descTag, Emit.descTag] <;> decide
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] using owned.descriptor.1
  · have bound : valueTag value < 2^8 := by cases value <;> dsimp only [valueTag, Emit.valueTag] <;> decide
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] using owned.valueStored.1
  · intro i hi j hj equal
    apply owned.readonly _ (Or.inl (Or.inl ⟨i, hi, rfl⟩))
    exact Or.inr (Or.inr (Or.inr (saved_span s _ ⟨j, hj, equal⟩)))
  · intro i hi j hj equal
    apply owned.readonly _ (Or.inr (Or.inl (Or.inl ⟨i, hi, rfl⟩)))
    exact Or.inr (Or.inr (Or.inr (saved_span s _ ⟨j, hj, equal⟩)))
  · apply jump_runs e base hc _ desc P rfl
    · exact owned.saved_table
    · exact next

theorem entry_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used ra : BitVec 64) (retain : Bool)
    (owned : Owned s base desc value buffer address capacity used ra retain) :
    Eventually (step e) (EntryPost s base desc value) (s, base) := by
  apply entry_cps e base hc s desc value buffer address capacity used ra retain owned
  exact Eventually.done _ ⟨rfl, entry_atBody s base desc value, entry_value_tag s base desc value⟩

end SszX86.Measure

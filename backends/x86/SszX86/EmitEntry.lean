import SszX86.EmitTypedDispatch

namespace SszX86.Emit
open SszNative.Serialize UintCodec

theorem Owned.push_mapped {s : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer ra : BitVec 64} {written : Nat} (owned : Owned s base desc value buffer ra written) :
    Large.Mapped s.dmem (s.regs.rsp.toBitVec - 48) 48 := by
  intro i hi
  have address : s.regs.rsp.toBitVec - 48 + BitVec.ofNat 64 i =
      s.regs.rsp.toBitVec - 160 + BitVec.ofNat 64 (112 + i) := by bv_omega
  rw [address]
  exact owned.stackMapped (112 + i) (by omega)

theorem Owned.borrowed_push_apart {s : MachineData} {base : Int64} {desc : Desc} {value : Value}
    {buffer ra : BitVec 64} {written : Nat} (owned : Owned s base desc value buffer ra written)
    (p : BitVec 64) (n : Nat)
    (borrowed : ∀ a, InSpan a p n → Borrowed s desc value buffer a) :
    ∀ i < n, ∀ j < 48, p + BitVec.ofNat 64 i ≠
      s.regs.rsp.toBitVec - 48 + BitVec.ofNat 64 j := by
  intro i hi j hj equal
  apply owned.readonly _ (borrowed _ ⟨i, hi, rfl⟩)
  right; right; right
  refine ⟨112 + j, by omega, ?_⟩
  rw [equal]
  bv_omega

/-- Original entry0, all six PUSHes, SUB104, descriptor/value loads, scalar
selection and actual indirect JMP. Every intermediate anchor is a conclusion. -/
theorem entry_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (desc : Desc) (value : Value) (buffer ra : BitVec 64) (written : Nat)
    (owned : Owned s base desc value buffer ra written) :
    Eventually (step e) (EntryPost s base desc value) (s, base) := by
  have descriptorNat : (BitVec.ofNat 64 (descTag desc)).toNat = descTag desc := by
    cases desc <;> dsimp only [descTag] <;> decide
  have valueNat : (BitVec.ofNat 8 (valueTag value)).toNat = valueTag value := by
    cases value <;> dsimp only [valueTag] <;> decide
  apply setup_runs e base hc s (BitVec.ofNat 64 (descTag desc))
    (BitVec.ofNat 8 (valueTag value)) _ owned.push_mapped
  · rw [descriptorNat]
    exact owned.descriptor.1
  · rw [valueNat]
    exact owned.valueStored.1
  · apply owned.borrowed_push_apart s.regs.rsi.toBitVec 8
    intro a inside
    left
    obtain ⟨i, hi, equal⟩ := inside
    refine ⟨i, ?_, equal⟩
    cases desc <;> simp only [descBytes] <;> omega
  · apply owned.borrowed_push_apart s.regs.rdx.toBitVec 1
    intro a inside
    right; left
    obtain ⟨i, hi, equal⟩ := inside
    refine ⟨i, ?_, equal⟩
    cases value <;> simp only [valueBytes] <;> omega
  · apply dispatch_typed e base hc s _ desc value
    · exact prepared_atBody _ _ _
    · rfl
    · change (BitVec.ofNat 8 (valueTag value)).setWidth 64 = BitVec.ofNat 64 (valueTag value)
      cases value <;> rfl
    · exact success_compatible desc value written owned.valid.success
    · exact owned.saved_table

end SszX86.Emit

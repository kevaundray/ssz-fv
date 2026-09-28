import SszX86.EmitBoolGuards

namespace SszX86.Emit
open BoolCodec UintCodec

def boolWritten (s : MachineData) (value : Bool) : MachineData :=
  {boolLoaded s value with
    dmem := Mem.storeInt
      (Mem.storeInt s.dmem s.regs.r14.toBitVec 1 (if value then 1 else 0))
      s.regs.rbx.toBitVec 8 1}

/-- Exactly the byte store, usize store, and jump to the common success tail. -/
theorem bool_stores (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (value : Bool) (P : MachineState → Prop)
    (output : Large.Mapped s.dmem s.regs.r14.toBitVec 1)
    (result : Large.Mapped s.dmem s.regs.rbx.toBitVec 8)
    (next : Eventually (step e) P (boolWritten s value, base + 1593)) :
    Eventually (step e) P (boolLoaded s value, base + 213) := by
  have outLoad : ∃ old, Mem.loadInt s.dmem s.regs.r14.toBitVec 1 = some old := by
    simpa only [BitVec.add_zero] using Large.mapped_load _ _ 1 0 1 output (by decide)
  cases value <;> simp only [boolLoaded, Bool.false_eq_true, ↓reduceIte]
  all_goals
    emit_step 47 using hc
    apply Delimited.store_cps
    · exact outLoad
    simp only [Effects.All]
    emit_step 48 using hc
    apply Delimited.store_cps
    · simpa only [BitVec.add_zero] using
        Large.mapped_load _ _ 8 0 8 (Large.mapped_store _ _ _ _ _ _ result) (by decide)
    simp only [Effects.All]
    emit_step 49 using hc
    simpa [boolWritten, boolLoaded] using next

end SszX86.Emit

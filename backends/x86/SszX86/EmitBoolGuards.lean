import SszX86.EmitCore

namespace SszX86.Emit
open BoolCodec

def boolValueTested (s : MachineData) (af : Bool) : MachineData :=
  {s with status :=
    StatusFlags.from_result (s.regs.rcx.toBitVec.take 32) {cf := false, af, of := false}}

def boolCapacityTested (s : MachineData) (af : Bool) : MachineData :=
  {s with status :=
    StatusFlags.from_result s.regs.r9.toBitVec {cf := false, af, of := false}}

theorem bool_value_guard (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (tag : s.regs.rcx.toBitVec = 0#64)
    (next : ∀ af, Eventually (step e) P (boolValueTested s af, base + 198)) :
    Eventually (step e) P (s, base + 190) := by
  have branch (af : Bool) : Eventually (step e) P (boolValueTested s af, base + 192) := by
    emit_step 43 using hc
    simpa [boolValueTested, StatusFlags.from_result, tag, Effects.All,
      show (0#64).take 32 = 0#32 by decide] using next af
  emit_step 42 using hc
  exact ⟨branch false, branch true⟩

theorem bool_capacity_guard (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (fits : s.regs.r9.toBitVec ≠ 0#64)
    (next : ∀ af, Eventually (step e) P (boolCapacityTested s af, base + 207)) :
    Eventually (step e) P (s, base + 198) := by
  have branch (af : Bool) : Eventually (step e) P (boolCapacityTested s af, base + 201) := by
    emit_step 45 using hc
    simpa [boolCapacityTested, StatusFlags.from_result, fits, Effects.All] using next af
  emit_step 44 using hc
  exact ⟨branch false, branch true⟩

def boolLoaded (s : MachineData) (value : Bool) : MachineData :=
  {s with regs := {s.regs with rax := if value then 1 else 0}}

theorem bool_payload_load (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (value : Bool) (P : MachineState → Prop)
    (stored : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 1) 1 = some (if value then 1 else 0))
    (next : Eventually (step e) P (boolLoaded s value, base + 213)) :
    Eventually (step e) P (s, base + 207) := by
  have one : (1 : BitVec 64) = 1#64 := by decide
  simp only [one] at stored
  emit_step 46 using hc
  cases value <;> simpa [MachineData.load, Effects.All, stored, boolLoaded,
    show (BitVec.ofInt 8 0).setWidth 64 = 0#64 by decide,
    show (BitVec.ofInt 8 1).setWidth 64 = 1#64 by decide] using next

end SszX86.Emit

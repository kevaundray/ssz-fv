import SszX86.MeasureEntryMemory
import SszX86.MeasureJump

namespace SszX86.Measure
open SszNative.Serialize

/-- Registers anchored by the original PUSH/SUB/tag-load/indirect-jump prefix. -/
structure AtBody (s t : MachineData) : Prop where
  memory : t.dmem = savedMem s
  stack : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 264
  result : t.regs.rbx = s.regs.rdi
  valuePointer : t.regs.r14 = s.regs.rdx
  descriptorPointer : t.regs.rsi = s.regs.rsi
  arenaPointer : t.regs.rcx = s.regs.rcx
  vectors : t.zmms = s.zmms

def entryState (s : MachineData) (base : Int64) (desc : Desc) (value : Value) : MachineData :=
  jumped (prepared s (BitVec.ofNat 64 (descTag desc)) (BitVec.ofNat 8 (valueTag value))) base desc

theorem entry_atBody (s : MachineData) (base : Int64) (desc : Desc) (value : Value) :
    AtBody s (entryState s base desc value) :=
  ⟨rfl, prepared_sp s (BitVec.ofNat 64 (descTag desc)) (BitVec.ofNat 8 (valueTag value)),
    rfl, rfl, rfl, rfl, rfl⟩

theorem entry_value_tag (s : MachineData) (base : Int64) (desc : Desc) (value : Value) :
    (entryState s base desc value).regs.rax.toBitVec.setWidth 8 = BitVec.ofNat 8 (valueTag value) := by
  cases value <;> rfl

def EntryPost (s : MachineData) (base : Int64) (desc : Desc) (value : Value)
    (t : MachineState) : Prop :=
  t.2 = base + Int64.ofNat (bodyEntry desc) ∧ AtBody s t.1 ∧
    t.1.regs.rax.toBitVec.setWidth 8 = BitVec.ofNat 8 (valueTag value)

end SszX86.Measure

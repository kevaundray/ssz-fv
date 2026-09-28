import SszX86.EmitOwnedMemory
import SszX86.EmitDispatch

namespace SszX86.Emit
open SszNative.Serialize

/-- Anchors established by the actual prologue, independent of undefined flags. -/
structure AtBody (s t : MachineData) : Prop where
  memory : t.dmem = savedMem s
  stack : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 152
  result : t.regs.rbx = s.regs.rdi
  output : t.regs.r14 = s.regs.r8
  valuePointer : t.regs.r12 = s.regs.rdx
  descriptorPointer : t.regs.rsi = s.regs.rsi
  capacity : t.regs.r9 = s.regs.r9
  vector : t.zmms = s.zmms

def bodyEntry : Desc → Nat
  | .bool => 190 | .uint _ => 50
  | .byteVector _ | .byteList _ => 256
  | .bitVector _ | .bitList _ | .progressiveBitList _ => 414

def BodyTag (desc : Desc) (value : Value) (t : MachineData) : Prop :=
  t.regs.rax.toBitVec = BitVec.ofNat 64 (descTag desc) ∧
  (descTag desc ≤ 1 → t.regs.rcx.toBitVec = BitVec.ofNat 64 (valueTag value))

theorem prepared_atBody (s : MachineData) (descriptor : BitVec 64) (value : BitVec 8) :
    AtBody s (prepared s descriptor value) :=
  ⟨rfl, prepared_sp s descriptor value, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem AtBody.tested {s t : MachineData} (h : AtBody s t) (af : Bool) :
    AtBody s (descriptorTested t af) :=
  ⟨h.memory, h.stack, h.result, h.output, h.valuePointer, h.descriptorPointer, h.capacity, h.vector⟩

theorem AtBody.compared {s t : MachineData} (h : AtBody s t) :
    AtBody s (descriptorCompared t) :=
  ⟨h.memory, h.stack, h.result, h.output, h.valuePointer, h.descriptorPointer, h.capacity, h.vector⟩

theorem AtBody.indexed {s t : MachineData} (h : AtBody s t) (kind : TableKind) :
    AtBody s (indexedState t kind) :=
  ⟨h.memory, h.stack, h.result, h.output, h.valuePointer, h.descriptorPointer, h.capacity, h.vector⟩

theorem AtBody.jumped {s t : MachineData} (h : AtBody s t) (base : Int64) (kind : TableKind) :
    AtBody s (jumped t base kind) :=
  ⟨h.memory, h.stack, h.result, h.output, h.valuePointer, h.descriptorPointer, h.capacity, h.vector⟩

def EntryPost (s : MachineData) (base : Int64) (desc : Desc) (value : Value)
    (t : MachineState) : Prop :=
  t.2 = base + Int64.ofNat (bodyEntry desc) ∧ AtBody s t.1 ∧ BodyTag desc value t.1

end SszX86.Emit

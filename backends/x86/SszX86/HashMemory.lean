import SszX86.HashImpl
import SszX86.EmitMemcpyMemory
import SszX86.MemsetProofs
import SszHashStreamMemory
import SszHashStreamPublic

namespace SszX86.Hash

abbrev Model := SszNative.HashStream.State
abbrev BytesAt := Emit.ListBytesAt
abbrev Mapped := UintCodec.Large.Mapped
abbrev Disjoint := UintCodec.Large.Disjoint
abbrev InSpan := Emit.InSpan
abbrev MemoryFrame := Emit.MemoryFrame

/-- Byte-exact native state layout, including stale buffer bytes. -/
def StateAt (m : DataMem) (p : BitVec 64) (state : Model) : Prop :=
  BytesAt m p (SszNative.HashStream.stateBytes state).toList

/-- The complete little-endian 32-byte chaining state. -/
def chainingBytes (state : Vector UInt32 8) : List UInt8 :=
  List.ofFn fun i : Fin 32 =>
    SszNative.HashStream.littleByte (state[i.val / 4]'(by omega)).toNat (i.val % 4)

def ChainingAt (m : DataMem) (p : BitVec 64) (state : Vector UInt32 8) : Prop :=
  BytesAt m p (chainingBytes state)

/-- No wrapping physical allocation. Empty inputs need not be mapped. -/
def Physical (p : BitVec 64) (size : Nat) : Prop :=
  p.toNat + size ≤ 2 ^ 64

/-- The owned local stack is below the incoming return slot. -/
def StackAt (m : DataMem) (sp : BitVec 64) (depth : Nat) : Prop :=
  depth ≤ sp.toNat ∧ Mapped m (sp - BitVec.ofNat 64 depth) depth

/-- System V callee-saved GPRs. Caller-saved vector registers are unconstrained. -/
def Saved (s t : MachineData) : Prop :=
  t.regs.rbx = s.regs.rbx ∧ t.regs.rbp = s.regs.rbp ∧
  t.regs.r12 = s.regs.r12 ∧ t.regs.r13 = s.regs.r13 ∧
  t.regs.r14 = s.regs.r14 ∧ t.regs.r15 = s.regs.r15

/-- Normal return through the original mapped slot, not a success frontier. -/
def Returned (s : MachineData) (ra : BitVec 64) (t : MachineState) : Prop :=
  t.2 = Int64.ofBitVec ra ∧
  t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 8 ∧ Saved s t.1

def ReturnAt (s : MachineData) (ra : BitVec 64) : Prop :=
  Physical s.regs.rsp.toBitVec 8 ∧
  Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))

theorem saved_refl (s : MachineData) : Saved s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem saved_trans {s t u : MachineData} (h : Saved s t) (h' : Saved t u) : Saved s u :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1,
   h'.2.2.2.1.trans h.2.2.2.1, h'.2.2.2.2.1.trans h.2.2.2.2.1,
   h'.2.2.2.2.2.trans h.2.2.2.2.2⟩

end SszX86.Hash

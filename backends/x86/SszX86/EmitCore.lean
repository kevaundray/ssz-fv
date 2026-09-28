import SszX86.EmitDecode
import SszSerializeProofs

namespace SszX86.Emit
open Kraken.X64.Parser
open BoolCodec UintCodec

abbrev step (e : Executable) := BoolCodec.step e

/-- A represented native Nat retains every original padding limb. -/
def NatAt (m : DataMem) (p : BitVec 64) (operand : SszNative.NatOperand) : Prop :=
  widthLoad m p.toNat 8 = some operand.pointer.toNat ∧
  widthLoad m (p.toNat + 8) 8 = some operand.payload.toNat ∧
  operand.At (widthLoad m)

/-- Output prefix observation does not demand any initial prefix values. -/
def BytesAt (m : DataMem) (p : BitVec 64) (bytes : Ssz.Bytes) : Prop :=
  ∀ i (hi : i < bytes.size), m.get? (p + BitVec.ofNat 64 i) = some bytes[i]

/-- A byte-exact frame; the caller may retain arbitrary unreadable old bytes. -/
def MemoryFrame (before after : DataMem) (writable : BitVec 64 → Prop) : Prop :=
  ∀ a, ¬ writable a → after.get? a = before.get? a

/-- Half-open physical span membership, including the empty span. -/
def InSpan (address pointer : BitVec 64) (physicalSize : Nat) : Prop :=
  ∃ i, i < physicalSize ∧ address = pointer + BitVec.ofNat 64 i

/-- Body writes are the live output prefix, result length, and local/call stack.
The six saved registers above the local area are excluded. -/
def BodyWritable (s : MachineData) (physicalSize : Nat) (a : BitVec 64) : Prop :=
  InSpan a s.regs.r14.toBitVec physicalSize ∨ InSpan a s.regs.rbx.toBitVec 8 ∨
  InSpan a (s.regs.rsp.toBitVec - 8) 112

/-- Common primitive endpoint immediately before the status-zero store. -/
structure BodyPost (s : MachineData) (bytes : Ssz.Bytes) (t : MachineData) : Prop where
  stack : t.regs.rsp = s.regs.rsp
  result : t.regs.rbx = s.regs.rbx
  length : widthLoad t.dmem s.regs.rbx.toNat 8 = some bytes.size
  output : BytesAt t.dmem s.regs.r14.toBitVec bytes
  frame : MemoryFrame s.dmem t.dmem (BodyWritable s bytes.size)
  vector : t.zmms = s.zmms

end SszX86.Emit

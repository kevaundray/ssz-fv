import SszX86.EmitModel
import SszX86.EmitReturnMemory

namespace SszX86.Emit
open SszNative SszNative.Serialize UintCodec

/-- Physical spans for the original primitive descriptor's represented fields. -/
def descBytes : Desc → Nat
  | .progressiveBitList _ => 32
  | _ => 24

def valueBytes : Value → Nat
  | .bits _ => 48
  | _ => 24

def DescPayloadAt (m : DataMem) (p : BitVec 64) : Desc → Prop
  | .bool => True
  | .uint operand | .byteVector operand | .byteList operand
  | .bitVector operand | .bitList operand => NatAt m (p + 8) operand
  | .progressiveBitList none =>
      Mem.loadInt m (p + 8) 4 = some 0
  | .progressiveBitList (some operand) =>
      Mem.loadInt m (p + 8) 4 = some 1 ∧ NatAt m (p + 16) operand

def DescAt (m : DataMem) (p : BitVec 64) (desc : Desc) : Prop :=
  Mem.loadInt m p 8 = some (descTag desc : Int) ∧ DescPayloadAt m p desc

def ValuePayloadAt (m : DataMem) (p buffer : BitVec 64) : Value → Prop
  | .bool value => Mem.loadInt m (p + 1) 1 = some (if value then 1 else 0)
  | .uint number => NatAt m (p + 8) number
  | .bytes bytes =>
      Mem.loadInt m (p + 8) 8 = some (buffer.toNat : Int) ∧
      Mem.loadInt m (p + 16) 8 = some (bytes.size : Int) ∧
      BytesAt m buffer bytes ∧ buffer.toNat + bytes.size ≤ 2 ^ 64
  | .bits bits =>
      Mem.loadInt m (p + 16) 8 = some (buffer.toNat : Int) ∧
      Mem.loadInt m (p + 24) 8 = some (bits.bytes.size : Int) ∧
      Mem.loadInt m (p + 32) 8 = some ((bits.count.setWidth 64).toNat : Int) ∧
      Mem.loadInt m (p + 40) 8 = some (((bits.count >>> (64 : Nat)).setWidth 64).toNat : Int) ∧
      BytesAt m buffer bits.bytes ∧ buffer.toNat + bits.bytes.size ≤ 2 ^ 64
  | .seq _ | .union _ _ => True

def ValueAt (m : DataMem) (p buffer : BitVec 64) (value : Value) : Prop :=
  Mem.loadInt m p 1 = some (valueTag value : Int) ∧ ValuePayloadAt m p buffer value

def NatBorrowed (operand : NatOperand) (address : BitVec 64) : Prop :=
  match operand with
  | .small _ => False
  | .large pointer limbs => InSpan address pointer (8 * limbs.length)

def DescBorrowed (desc : Desc) (address : BitVec 64) : Prop :=
  match desc with
  | .bool | .progressiveBitList none => False
  | .uint operand | .byteVector operand | .byteList operand
  | .bitVector operand | .bitList operand | .progressiveBitList (some operand) =>
      NatBorrowed operand address

def ValueBorrowed (value : Value) (buffer address : BitVec 64) : Prop :=
  match value with
  | .uint number => NatBorrowed number address
  | .bytes bytes => InSpan address buffer bytes.size
  | .bits bits => InSpan address buffer bits.bytes.size
  | _ => False

/-- Full original physical observations, including every padding limb. No two
readonly members of this footprint need be disjoint. -/
def Borrowed (s : MachineData) (desc : Desc) (value : Value) (buffer address : BitVec 64) : Prop :=
  InSpan address s.regs.rsi.toBitVec (descBytes desc) ∨
  InSpan address s.regs.rdx.toBitVec (valueBytes value) ∨
  DescBorrowed desc address ∨ ValueBorrowed value buffer address

/-- Exact public success-write regions. Capacity beyond the live prefix is not
writable; result padding and the caller return slot are likewise excluded. -/
def Writable (s : MachineData) (written : Nat) (address : BitVec 64) : Prop :=
  InSpan address s.regs.r8.toBitVec written ∨
  InSpan address s.regs.rdi.toBitVec 8 ∨
  InSpan address (s.regs.rdi.toBitVec + 64) 4 ∨
  InSpan address (s.regs.rsp.toBitVec - 160) 160

/-- Original private-entry ownership and successful logical call only. The
optional Plan pointer in RCX has deliberately no readable-memory premise. -/
structure Owned (s : MachineData) (base : Int64) (desc : Desc) (value : Value)
    (buffer ra : BitVec 64) (written : Nat) : Prop where
  valid : ValidCall desc value s.regs.r9.toNat written
  physical : value.Physical
  descriptor : DescAt s.dmem s.regs.rsi.toBitVec desc
  valueStored : ValueAt s.dmem s.regs.rdx.toBitVec buffer value
  descriptorBound : s.regs.rsi.toNat + descBytes desc ≤ 2 ^ 64
  valueBound : s.regs.rdx.toNat + valueBytes value ≤ 2 ^ 64
  outputBound : s.regs.r8.toNat + s.regs.r9.toNat ≤ 2 ^ 64
  resultBound : s.regs.rdi.toNat + 80 ≤ 2 ^ 64
  stackLow : 160 ≤ s.regs.rsp.toNat
  returnBound : s.regs.rsp.toNat + 8 ≤ 2 ^ 64
  outputMapped : Large.Mapped s.dmem s.regs.r8.toBitVec written
  lengthMapped : Large.Mapped s.dmem s.regs.rdi.toBitVec 8
  statusMapped : Large.Mapped s.dmem (s.regs.rdi.toBitVec + 64) 4
  stackMapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 160) 160
  returnSlot : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))
  outputResult : Large.Disjoint s.regs.r8.toBitVec s.regs.rdi.toBitVec written 80
  outputStack : Large.Disjoint s.regs.r8.toBitVec (s.regs.rsp.toBitVec - 160) written 168
  resultStack : Large.Disjoint s.regs.rdi.toBitVec (s.regs.rsp.toBitVec - 160) 80 168
  tailReadonly : ∀ i, written ≤ i → i < s.regs.r9.toNat →
    ¬ (InSpan (s.regs.r8.toBitVec + BitVec.ofNat 64 i) s.regs.rdi.toBitVec 8 ∨
      InSpan (s.regs.r8.toBitVec + BitVec.ofNat 64 i) (s.regs.rdi.toBitVec + 64) 4 ∨
      InSpan (s.regs.r8.toBitVec + BitVec.ofNat 64 i) (s.regs.rsp.toBitVec - 160) 160)
  readonly : ∀ address, Borrowed s desc value buffer address → ¬ Writable s written address
  table : TableAt s.dmem base
  tableReadonly : ∀ address, InSpan address (tableAddress base) 16 → ¬ Writable s written address

end SszX86.Emit

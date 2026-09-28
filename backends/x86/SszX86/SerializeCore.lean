import SszX86.SerializeDecode
import SszX86.BitVectorMappingClosure

namespace SszX86.Serialize
open SszNative SszNative.Serialize UintCodec

abbrev InSpan := Emit.InSpan
abbrev MemoryFrame := Emit.MemoryFrame
abbrev arenaState := Measure.arenaState

/-- The original wrapper reserves 96 bytes after five pushes. Its Plan occupies
exactly 72 bytes and ends at the first saved register, not eight bytes later. -/
def stackBase (s : MachineData) : BitVec 64 := s.regs.rsp.toBitVec - 424
def wrapperSP (s : MachineData) : BitVec 64 := s.regs.rsp.toBitVec - 136
def planPointer (s : MachineData) : BitVec 64 := s.regs.rsp.toBitVec - 112

def written (s : MachineData) (desc : Desc) (value : Value)
    (address capacity used : BitVec 64) : Written :=
  SszNative.Serialize.serialize desc value s.regs.r8.toNat (arenaState address capacity used)

/-- Only active enum observations are claimed as original borrowed input. The
primitive projection of Seq/Union observes its tag, not a native recursive tree. -/
def Borrowed (s : MachineData) (desc : Desc) (value : Value)
    (buffer a : BitVec 64) : Prop :=
  Measure.Borrowed s desc value buffer a

/-- Original physical regions, before any PUSH or callee execution. -/
def Reserved (s : MachineData) (address capacity used a : BitVec 64) : Prop :=
  InSpan a s.regs.rdi.toBitVec 80 ∨ InSpan a s.regs.rcx.toBitVec s.regs.r8.toNat ∨
  InSpan a (s.regs.r9.toBitVec + 16) 8 ∨
  InSpan a (address + used) (capacity.toNat - used.toNat) ∨ InSpan a (stackBase s) 424

structure Owned (s : MachineData) (base : Int64) (desc : Desc) (value : Value)
    (buffer address capacity used ra : BitVec 64) : Prop where
  physical : value.Physical
  descriptor : Emit.DescAt s.dmem s.regs.rsi.toBitVec desc
  descriptorMapped : Large.Mapped s.dmem s.regs.rsi.toBitVec (Emit.descBytes desc)
  valueStored : Emit.ValueAt s.dmem s.regs.rdx.toBitVec buffer value
  arena : Measure.ArenaAt s.dmem s.regs.r9.toBitVec address capacity used
  descriptorBound : s.regs.rsi.toNat + Emit.descBytes desc ≤ 2 ^ 64
  valueBound : s.regs.rdx.toNat + Emit.valueBytes value ≤ 2 ^ 64
  resultBound : s.regs.rdi.toNat + 80 ≤ 2 ^ 64
  outputBound : s.regs.rcx.toNat + s.regs.r8.toNat ≤ 2 ^ 64
  headerBound : s.regs.r9.toNat + 24 ≤ 2 ^ 64
  stackLow : 424 ≤ s.regs.rsp.toNat
  returnBound : s.regs.rsp.toNat + 8 ≤ 2 ^ 64
  arenaBound : address.toNat + capacity.toNat ≤ 2 ^ 64
  arenaNonzero : 0 < capacity.toNat → 0 < address.toNat
  resultMapped : Large.Mapped s.dmem s.regs.rdi.toBitVec 80
  outputMapped : Large.Mapped s.dmem s.regs.rcx.toBitVec s.regs.r8.toNat
  stackMapped : Large.Mapped s.dmem (stackBase s) 424
  freeMapped : Large.Mapped s.dmem (address + used) (capacity.toNat - used.toNat)
  returnSlot : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 =
    some (Int.ofBytes (wordBytes ra))
  resultHeader : Large.Disjoint s.regs.rdi.toBitVec s.regs.r9.toBitVec 80 24
  resultStack : Large.Disjoint s.regs.rdi.toBitVec (stackBase s) 80 432
  outputResult : Large.Disjoint s.regs.rcx.toBitVec s.regs.rdi.toBitVec s.regs.r8.toNat 80
  outputStack : Large.Disjoint s.regs.rcx.toBitVec (stackBase s) s.regs.r8.toNat 432
  outputHeader : Large.Disjoint s.regs.rcx.toBitVec s.regs.r9.toBitVec s.regs.r8.toNat 24
  headerStack : Large.Disjoint s.regs.r9.toBitVec (stackBase s) 24 432
  freeResult : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rdi.toNat 80
  freeOutput : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rcx.toNat s.regs.r8.toNat
  freeHeader : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.r9.toNat 24
  freeStack : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    (s.regs.rsp.toNat - 424) 432
  readonly : ∀ a, Emit.Borrowed s desc value buffer a → ¬ Reserved s address capacity used a
  measureTable : Measure.TableAt s.dmem (base + Int64.ofInt measureOffset)
  emitTable : Emit.TableAt s.dmem (base + Int64.ofInt emitOffset)
  measureTableReadonly : ∀ a,
    InSpan a (Measure.tableAddress (base + Int64.ofInt measureOffset)) 52 →
      ¬ Reserved s address capacity used a
  emitTableReadonly : ∀ a,
    InSpan a (Emit.tableAddress (base + Int64.ofInt emitOffset)) 16 →
      ¬ Reserved s address capacity used a

def ResultAt (observe : Nat → Nat → Option Nat) (out : Nat) : Except Error Nat → Prop
  | .ok n => observe out 8 = some n ∧ observe (out + 64) 4 = some 0
  | .error reason => Measure.ErrorAt observe out reason

/-- Measurement failures copy 72 bytes, including the actual arbitrary padding
word. Host/capacity failures write 68; successful emit writes only 8+4. -/
def ResultWrites (out : BitVec 64) (measured : Outcome NatOperand)
    (result : Except Error Nat) (a : BitVec 64) : Prop :=
  match measured.result, result with
  | .error _, _ => InSpan a out 72
  | .ok _, .error _ => InSpan a out 68
  | .ok _, .ok _ => InSpan a out 8 ∨ InSpan a (out + 64) 4

def Writable (s : MachineData) (desc : Desc) (value : Value)
    (address capacity used a : BitVec 64) : Prop :=
  let measured := SszNative.Serialize.measure desc value (arenaState address capacity used)
  let final := written s desc value address capacity used
  ResultWrites s.regs.rdi.toBitVec measured final.outcome.result a ∨
  InSpan a s.regs.rcx.toBitVec final.writes.size ∨
  Measure.AllocationWrites final.outcome.calls a ∨
  (Measure.Allocated final.outcome.calls ∧ InSpan a (s.regs.r9.toBitVec + 16) 8) ∨
  InSpan a (stackBase s) 424

structure Post (s : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used ra : BitVec 64) (t : MachineState) : Prop where
  abi : Measure.ABI s ra t
  observed : ResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
    (written s desc value address capacity used).outcome.result
  cursor : widthLoad t.1.dmem (s.regs.r9.toNat + 16) 8 =
    some (written s desc value address capacity used).outcome.used
  header : widthLoad t.1.dmem s.regs.r9.toNat 8 = some address.toNat ∧
    widthLoad t.1.dmem (s.regs.r9.toNat + 8) 8 = some capacity.toNat
  calls : Measure.CallsAt (widthLoad t.1.dmem)
    (written s desc value address capacity used).outcome.calls
  descriptor : Emit.DescAt t.1.dmem s.regs.rsi.toBitVec desc
  valueStored : Emit.ValueAt t.1.dmem s.regs.rdx.toBitVec buffer value
  borrowedFrame : ∀ a, Borrowed s desc value buffer a → t.1.dmem.get? a = s.dmem.get? a
  outputFrame : ∀ i < s.regs.r8.toNat,
    t.1.dmem.get? (s.regs.rcx.toBitVec + BitVec.ofNat 64 i) =
      applyWrites (fun j => s.dmem.get? (s.regs.rcx.toBitVec + BitVec.ofNat 64 j))
        (written s desc value address capacity used).writes i
  frame : MemoryFrame s.dmem t.1.dmem (Writable s desc value address capacity used)

theorem measured_valid (desc : Desc) (value : Value)
    (address capacity used : BitVec 64) (operand : NatOperand)
    (physical : value.Physical)
    (measured : (SszNative.Serialize.measure desc value (arenaState address capacity used)).result =
      .ok operand) (host : operand.value < 2 ^ 64) :
    Emit.ValidCall desc value operand.value operand.value := by
  have sized : (encodedSize desc value (arenaState address capacity used)).result =
      .ok operand.value := by
    simp only [encodedSize, SszNative.Serialize.bind, measured, hostSize, host,
      ↓reduceIte, unchanged]
  exact ⟨encodedSize_success desc value (arenaState address capacity used)
    physical operand.value sized, host, Nat.le_refl _⟩

end SszX86.Serialize

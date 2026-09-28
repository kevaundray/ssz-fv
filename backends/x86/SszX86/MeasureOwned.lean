import SszX86.MeasureCore
import SszX86.NatCompareProofs

namespace SszX86.Measure
open SszNative SszNative.Serialize UintCodec

/-- Actual separately verified helper code at this measure image's linked offsets. -/
structure HelpersAt (e : Executable) (base : Int64) : Prop where
  compare : NatCompare.CodeAt e (base + Int64.ofInt compareOffset)
  fromU128 : NatFromU128.CodeAt e (base + Int64.ofInt fromU128Offset)

def Borrowed (s : MachineData) (desc : Desc) (value : Value)
    (buffer address : BitVec 64) : Prop :=
  DescLive s.regs.rsi.toBitVec desc address ∨
  ValueLive s.regs.rdx.toBitVec value address ∨
  DescBorrowed desc address ∨ ValueBorrowed value buffer address

def Writable (s : MachineData) (outcome : Outcome NatOperand)
    (address : BitVec 64) : Prop :=
  ResultWrites s.regs.rdi.toBitVec outcome address ∨
  AllocationWrites outcome.calls address ∨
  (Allocated outcome.calls ∧ InSpan address (s.regs.rcx.toBitVec + 16) 8) ∨
  InSpan address (s.regs.rsp.toBitVec - 280) 280

/-- Ownership at original PC0, before PUSH, with either retain flag. The logical
measure outcome is not constrained. In particular used may exceed capacity. -/
structure Owned (s : MachineData) (base : Int64) (desc : Desc) (value : Value)
    (buffer address capacity used ra : BitVec 64) (retain : Bool) : Prop where
  physical : value.Physical
  descriptor : DescAt s.dmem s.regs.rsi.toBitVec desc
  descriptorMapped : Large.Mapped s.dmem s.regs.rsi.toBitVec (descBytes desc)
  valueStored : ValueAt s.dmem s.regs.rdx.toBitVec buffer value
  retainFlag : s.regs.r8.toBitVec.setWidth 8 = BitVec.ofNat 8 (if retain then 1 else 0)
  arena : ArenaAt s.dmem s.regs.rcx.toBitVec address capacity used
  descriptorBound : s.regs.rsi.toNat + descBytes desc ≤ 2 ^ 64
  valueBound : s.regs.rdx.toNat + valueBytes value ≤ 2 ^ 64
  resultBound : s.regs.rdi.toNat + 72 ≤ 2 ^ 64
  headerBound : s.regs.rcx.toNat + 24 ≤ 2 ^ 64
  stackLow : 280 ≤ s.regs.rsp.toNat
  returnBound : s.regs.rsp.toNat + 8 ≤ 2 ^ 64
  arenaBound : address.toNat + capacity.toNat ≤ 2 ^ 64
  arenaNonzero : 0 < capacity.toNat → 0 < address.toNat
  resultMapped : Large.Mapped s.dmem s.regs.rdi.toBitVec 72
  stackMapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 280) 280
  freeMapped : Large.Mapped s.dmem (address + used) (capacity.toNat - used.toNat)
  returnSlot : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 =
    some (Int.ofBytes (wordBytes ra))
  resultHeader : Large.Disjoint s.regs.rdi.toBitVec s.regs.rcx.toBitVec 72 24
  resultStack : Large.Disjoint s.regs.rdi.toBitVec (s.regs.rsp.toBitVec - 280) 72 288
  headerStack : Large.Disjoint s.regs.rcx.toBitVec (s.regs.rsp.toBitVec - 280) 24 288
  freeResult : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rdi.toNat 72
  freeHeader : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rcx.toNat 24
  freeStack : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    (s.regs.rsp.toNat - 280) 288
  readonly : ∀ a, Borrowed s desc value buffer a →
    ¬ (InSpan a s.regs.rdi.toBitVec 72 ∨ InSpan a (s.regs.rcx.toBitVec + 16) 8 ∨
      InSpan a (address + used) (capacity.toNat - used.toNat) ∨
      InSpan a (s.regs.rsp.toBitVec - 280) 280)
  table : TableAt s.dmem base
  tableReadonly : ∀ a, InSpan a (tableAddress base) 52 →
    ¬ (InSpan a s.regs.rdi.toBitVec 72 ∨ InSpan a (s.regs.rcx.toBitVec + 16) 8 ∨
      InSpan a (address + used) (capacity.toNat - used.toNat) ∨
      InSpan a (s.regs.rsp.toBitVec - 280) 280)

/-- SysV callee-saved registers and vector state, after the original RET. RAX is
not specified as an sret pointer: the actual primitive paths do not promise it. -/
structure ABI (s : MachineData) (ra : BitVec 64) (t : MachineState) : Prop where
  returned : t.2 = Int64.ofBitVec ra
  stack : t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 8
  rbx : t.1.regs.rbx = s.regs.rbx
  rbp : t.1.regs.rbp = s.regs.rbp
  r12 : t.1.regs.r12 = s.regs.r12
  r13 : t.1.regs.r13 = s.regs.r13
  r14 : t.1.regs.r14 = s.regs.r14
  r15 : t.1.regs.r15 = s.regs.r15
  vectors : t.1.zmms = s.zmms

/-- Wrapper-usable exact native outcome, committed cursor, allocation payloads,
original represented inputs, narrow publication footprint, and real return ABI. -/
structure Post (s : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used ra : BitVec 64) (t : MachineState) : Prop where
  abi : ABI s ra t
  observed : ResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
    (measure desc value (arenaState address capacity used)).result
  cursor : widthLoad t.1.dmem (s.regs.rcx.toNat + 16) 8 =
    some (measure desc value (arenaState address capacity used)).used
  header : widthLoad t.1.dmem s.regs.rcx.toNat 8 = some address.toNat ∧
    widthLoad t.1.dmem (s.regs.rcx.toNat + 8) 8 = some capacity.toNat
  calls : CallsAt (widthLoad t.1.dmem)
    (measure desc value (arenaState address capacity used)).calls
  descriptor : DescAt t.1.dmem s.regs.rsi.toBitVec desc
  valueStored : ValueAt t.1.dmem s.regs.rdx.toBitVec buffer value
  frame : MemoryFrame s.dmem t.1.dmem
    (Writable s (measure desc value (arenaState address capacity used)))

end SszX86.Measure

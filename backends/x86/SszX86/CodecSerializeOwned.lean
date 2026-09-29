import SszX86.CodecSerializeCode
import SszX86.CodecMeasureOwned
import SszX86.CodecEmitOwned
import SszX86.SerializeStack
import SszCodecEmitProofs

set_option autoImplicit false

namespace SszX86.CodecSerialize
open SszNative UintCodec

/-- Both recursive callees start 144 bytes below the original wrapper SP. The
measurement allowance subsumes the emitter's160-byte leaf helper allowance. -/
def stackBytes (desc : SszNative.Codec.Desc) : Nat :=
  144 + CodecMeasure.stackBytes desc

def stackBase (s : MachineData) (desc : SszNative.Codec.Desc) : BitVec 64 :=
  s.regs.rsp.toBitVec - BitVec.ofNat 64 (stackBytes desc)

def planPointer (s : MachineData) : BitVec 64 := s.regs.rsp.toBitVec - 112

def measured (desc : SszNative.Codec.Desc)
    (value : SszNative.Codec.Value) (address capacity used : BitVec 64) :
    SszNative.CodecMeasure.Outcome SszNative.CodecMeasure.Plan :=
  SszNative.CodecMeasure.measure desc value (Measure.arenaState address capacity used) true

def written (s : MachineData) (desc : SszNative.Codec.Desc)
    (value : SszNative.Codec.Value) (address capacity used : BitVec 64) :
    SszNative.CodecEmit.Written :=
  SszNative.CodecEmit.serialize desc value s.regs.r8.toNat
    (Measure.arenaState address capacity used)

/-- Actual linked callee code, not a semantic call contract or recursion oracle. -/
structure ClosureAt (e : Executable) (base : Int64) : Prop where
  wrapper : CodeAt e base
  measure : CodecMeasure.CodeAt e (base + Int64.ofInt measureOffset)
  measureHelpers : CodecMeasure.HelpersAt e (base + Int64.ofInt measureOffset)
  emitHelpers : CodecEmit.HelpersAt e (base + Int64.ofInt emitOffset)

def Available (s : MachineData) (desc : SszNative.Codec.Desc)
    (address capacity used : BitVec 64) : Codec.Footprint := fun a =>
  Codec.InSpan a s.regs.rdi.toBitVec 72 ∨
  Codec.InSpan a s.regs.rcx.toBitVec s.regs.r8.toNat ∨
  Codec.InSpan a (s.regs.r9.toBitVec + 16) 8 ∨
  Codec.InSpan a (address + used) (capacity.toNat - used.toNat) ∨
  Codec.StackWrites s.regs.rsp.toBitVec (stackBytes desc) a

/-- Original serialize ABI: raw recursive inputs, caller output, caller arena
and finite recursion-aware stack. There is no schema or measurement-success
premise. Readonly input graphs and constant tables may alias each other. -/
structure Owned (s : MachineData) (base : Int64) (desc : SszNative.Codec.Desc)
    (value : SszNative.Codec.Value) (readonly : Codec.Footprint)
    (address capacity used ra : BitVec 64) : Prop where
  physical : value.Physical
  descriptor : Codec.DescAt s.dmem readonly s.regs.rsi.toBitVec desc
  valueStored : Codec.ValueAt s.dmem readonly s.regs.rdx.toBitVec value
  descriptorMapped : Large.Mapped s.dmem s.regs.rsi.toBitVec 40
  valueMapped : Large.Mapped s.dmem s.regs.rdx.toBitVec 48
  arena : Measure.ArenaAt s.dmem s.regs.r9.toBitVec address capacity used
  usedBound : used.toNat ≤ capacity.toNat
  arenaBound : address.toNat + capacity.toNat ≤ 2^64
  arenaNonzero : 0 < capacity.toNat → 0 < address.toNat
  arenaMapped : Large.Mapped s.dmem address capacity.toNat
  resultBound : s.regs.rdi.toNat + 72 ≤ 2^64
  resultMapped : Large.Mapped s.dmem s.regs.rdi.toBitVec 72
  outputBound : s.regs.rcx.toNat + s.regs.r8.toNat ≤ 2^64
  outputMapped : Large.Mapped s.dmem s.regs.rcx.toBitVec s.regs.r8.toNat
  headerBound : s.regs.r9.toNat + 24 ≤ 2^64
  stack : Codec.StackAt s.dmem s.regs.rsp.toBitVec (stackBytes desc)
  stackAligned : s.regs.rsp.toNat % 8 = 0
  returnBound : s.regs.rsp.toNat + 8 ≤ 2^64
  returnSlot : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 =
    some (Int.ofBytes (wordBytes ra))
  resultHeader : Large.Disjoint s.regs.rdi.toBitVec s.regs.r9.toBitVec 72 24
  resultStack : Large.Disjoint s.regs.rdi.toBitVec (stackBase s desc) 72 (stackBytes desc + 8)
  outputResult : Large.Disjoint s.regs.rcx.toBitVec s.regs.rdi.toBitVec s.regs.r8.toNat 72
  outputStack : Large.Disjoint s.regs.rcx.toBitVec (stackBase s desc)
    s.regs.r8.toNat (stackBytes desc + 8)
  outputHeader : Large.Disjoint s.regs.rcx.toBitVec s.regs.r9.toBitVec s.regs.r8.toNat 24
  headerStack : Large.Disjoint s.regs.r9.toBitVec (stackBase s desc) 24 (stackBytes desc + 8)
  freeResult : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rdi.toNat 72
  freeOutput : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.rcx.toNat s.regs.r8.toNat
  freeHeader : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    s.regs.r9.toNat 24
  freeStack : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat)
    (s.regs.rsp.toNat - stackBytes desc) (stackBytes desc + 8)
  readonlyDisjoint : ∀ a, readonly a → ¬ Available s desc address capacity used a
  measureTable : CodecMeasure.TableAt s.dmem (base + Int64.ofInt measureOffset)
  measureTableReadonly : ∀ a,
    Codec.InSpan a (CodecMeasure.tableAddress (base + Int64.ofInt measureOffset)) 52 → readonly a
  emitTable : CodecEmit.TableAt s.dmem (base + Int64.ofInt emitOffset)
  emitTableReadonly : ∀ a,
    Codec.InSpan a (CodecEmit.tableAddress (base + Int64.ofInt emitOffset)) 16 → readonly a
  emitPartsTable : CodecEmit.Table1At s.dmem (base + Int64.ofInt emitOffset)
  emitPartsTableReadonly : ∀ a,
    Codec.InSpan a (CodecEmit.table1Address (base + Int64.ofInt emitOffset)) 20 → readonly a
  classifierTable : CodecIsFixed.TableAt s.dmem
    ((base + Int64.ofInt measureOffset) + Int64.ofInt CodecMeasure.isFixedOffset)
  classifierTableReadonly : ∀ a, Codec.InSpan a
    (CodecIsFixed.tableAddress ((base + Int64.ofInt measureOffset) +
      Int64.ofInt CodecMeasure.isFixedOffset)) 48 → readonly a

def ResultAt (observe : Nat → Nat → Option Nat) (out : Nat) :
    Except SszNative.CodecEmit.Fault Nat → Prop
  | .ok size => observe out 8 = some size ∧ observe (out + 64) 4 = some 0
  | .error (.returned reason) => Codec.ErrorAt observe out reason
  | .error (.bounds _ _ _) | .error .fieldIndex => False

def ResultWrites (out : BitVec 64)
    (measurement : Except SszNative.Codec.Error SszNative.CodecMeasure.Plan)
    (result : Except SszNative.CodecEmit.Fault Nat) : Codec.Footprint := fun a =>
  match measurement, result with
  | .error _, _ => Codec.InSpan a out 72
  | .ok _, .error _ => Codec.InSpan a out 68
  | .ok _, .ok _ => Codec.InSpan a out 8 ∨ Codec.InSpan a (out + 64) 4

def OutputWrites (out : BitVec 64) (writes : List SszNative.CodecEmit.Write) :
    Codec.Footprint := fun a =>
  ∃ write ∈ writes, Codec.InSpan a (out + BitVec.ofNat 64 write.address) write.bytes.size

def Writable (s : MachineData) (desc : SszNative.Codec.Desc)
    (value : SszNative.Codec.Value) (address capacity used : BitVec 64) :
    Codec.Footprint := fun a =>
  ResultWrites s.regs.rdi.toBitVec (measured desc value address capacity used).result
    (written s desc value address capacity used).result a ∨
  OutputWrites s.regs.rcx.toBitVec (written s desc value address capacity used).writes a ∨
  CodecMeasure.EffectsWrite (written s desc value address capacity used).effects a ∨
  Codec.InSpan a (s.regs.r9.toBitVec + 16) 8 ∨
  Codec.StackWrites s.regs.rsp.toBitVec (stackBytes desc) a

/-- Exact original-entry outcome. The checked serialize trace has relative
output addresses; its memory interpretation is anchored at the original caller
buffer, including unchanged suffix bytes and every native failure. -/
structure Post (s : MachineData) (desc : SszNative.Codec.Desc)
    (value : SszNative.Codec.Value) (readonly : Codec.Footprint)
    (address capacity used ra : BitVec 64) (t : MachineState) : Prop where
  abi : Measure.ABI s ra t
  observed : ResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
    (written s desc value address capacity used).result
  cursor : widthLoad t.1.dmem (s.regs.r9.toNat + 16) 8 =
    some (written s desc value address capacity used).used
  header : widthLoad t.1.dmem s.regs.r9.toNat 8 = some address.toNat ∧
    widthLoad t.1.dmem (s.regs.r9.toNat + 8) 8 = some capacity.toNat
  effects : CodecMeasure.EffectsAt t.1.dmem
    (CodecMeasure.ResultFootprint readonly (planPointer s)
      (written s desc value address capacity used).effects)
    (written s desc value address capacity used).effects
  descriptor : Codec.DescAt t.1.dmem readonly s.regs.rsi.toBitVec desc
  valueStored : Codec.ValueAt t.1.dmem readonly s.regs.rdx.toBitVec value
  output : ∀ i < s.regs.r8.toNat,
    t.1.dmem.get? (s.regs.rcx.toBitVec + BitVec.ofNat 64 i) =
      SszNative.CodecEmit.applyWrites
        (fun j => s.dmem.get? (s.regs.rcx.toBitVec + BitVec.ofNat 64 j))
        (written s desc value address capacity used).writes i
  frame : Codec.MemoryFrame s.dmem t.1.dmem (Writable s desc value address capacity used)

end SszX86.CodecSerialize

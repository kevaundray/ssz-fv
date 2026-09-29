import SszX86.CodecEmitInvariant
import SszX86.CodecEmitMemory
import SszX86.CodecEmitPartsStorage
import SszX86.CodecStack
import SszX86.CodecEmitImpl
import SszX86.CodecEmitPartsImpl
import SszX86.CodecIsFixedImpl
import SszX86.NatCompareImpl
import SszX86.EmitMemcpyEmbedded

set_option autoImplicit false

namespace SszX86.CodecEmit
open SszNative UintCodec

/-- Every active helper is bound to its actual linked address. This records only
instruction fetch/target facts; there is no semantic helper or recursive oracle. -/
structure HelpersAt (e : Executable) (base : Int64) : Prop where
  emit : CodeAt e base
  parts : CodecEmitParts.CodeAt e (base + 1712)
  fixed : CodecIsFixed.CodeAt e (base + 2800)
  compare : NatCompare.CodeAt e (base - 36416)
  copy : Emit.MemcpyCodeAt e (base + 110736)

/-- Stack demand grows with the finite declaration, not logical Nat magnitudes.
The common per-layer allowance covers nested emit/parts/is_fixed activations;
160 bytes separately cover the immutable primitive emitter provider. -/
def stackBytes (desc : SszNative.Codec.Desc) : Nat :=
  SszX86.Codec.descriptorStackBytes desc 160

def Writable (s : MachineData) (desc : SszNative.Codec.Desc) (written : Nat)
    (a : BitVec 64) : Prop :=
  Emit.InSpan a s.regs.r8.toBitVec written ∨
  Emit.InSpan a s.regs.rdi.toBitVec 8 ∨
  Emit.InSpan a (s.regs.rdi.toBitVec + 64) 4 ∨
  SszX86.Codec.StackWrites s.regs.rsp.toBitVec (stackBytes desc) a

/-- Original private-entry resources. The sole logical safety premise is the
past-generated plan. Result storage is exactly the actual 72-byte ABI area,
with only active success fields required mapped; padding stays unobserved. -/
structure Owned (s : MachineData) (base : Int64) (desc : SszNative.Codec.Desc)
    (value : SszNative.Codec.Value) (supplied : Option SszNative.CodecMeasure.Plan)
    (r : SszX86.Codec.Footprint) (ra : BitVec 64) where
  call : GeneratedCall desc value supplied s.regs.r9.toNat
  physical : value.Physical
  descriptor : SszX86.Codec.DescAt s.dmem r s.regs.rsi.toBitVec desc
  valueStored : SszX86.Codec.ValueAt s.dmem r s.regs.rdx.toBitVec value
  planStored : CodecEmitParts.OptionPlanAt s.dmem r s.regs.rcx.toBitVec supplied
  outputBound : s.regs.r8.toNat + s.regs.r9.toNat ≤ 2 ^ 64
  resultBound : s.regs.rdi.toNat + 72 ≤ 2 ^ 64
  returnBound : s.regs.rsp.toNat + 8 ≤ 2 ^ 64
  stack : SszX86.Codec.StackAt s.dmem s.regs.rsp.toBitVec (stackBytes desc)
  outputMapped : Large.Mapped s.dmem s.regs.r8.toBitVec call.measured.size.value
  lengthMapped : Large.Mapped s.dmem s.regs.rdi.toBitVec 8
  statusMapped : Large.Mapped s.dmem (s.regs.rdi.toBitVec + 64) 4
  returnSlot : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))
  outputResult : Large.Disjoint s.regs.r8.toBitVec s.regs.rdi.toBitVec s.regs.r9.toNat 72
  outputStack : Large.Disjoint s.regs.r8.toBitVec
    (s.regs.rsp.toBitVec - BitVec.ofNat 64 (stackBytes desc))
    s.regs.r9.toNat (stackBytes desc + 8)
  resultStack : Large.Disjoint s.regs.rdi.toBitVec
    (s.regs.rsp.toBitVec - BitVec.ofNat 64 (stackBytes desc)) 72 (stackBytes desc + 8)
  readonly : ∀ a, r a → ¬ Writable s desc call.measured.size.value a
  table : TableAt s.dmem base
  partsTable : Table1At s.dmem base
  classifierTable : CodecIsFixed.TableAt s.dmem (base + 2800)
  tableReadonly : ∀ a, Emit.InSpan a (tableAddress base) 16 →
    ¬ Writable s desc call.measured.size.value a
  partsTableReadonly : ∀ a, Emit.InSpan a (table1Address base) 20 →
    ¬ Writable s desc call.measured.size.value a
  classifierTableReadonly : ∀ a,
    Emit.InSpan a (CodecIsFixed.tableAddress (base + 2800)) 48 →
    ¬ Writable s desc call.measured.size.value a

/-- Observable private return: exact shared ordered writes, untouched suffix,
byte-exact exterior frame, active success result, and the complete SysV ABI.
No result padding, discarded plan, or untouched output byte is initialized. -/
structure Post (s : MachineData) (desc : SszNative.Codec.Desc)
    (value : SszNative.Codec.Value) (supplied : Option SszNative.CodecMeasure.Plan)
    (ra : BitVec 64) (written : Nat) (t : MachineState) : Prop where
  pc : t.2 = Int64.ofBitVec ra
  stack : t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 8
  rbx : t.1.regs.rbx.toBitVec = s.regs.rbx.toBitVec
  rbp : t.1.regs.rbp.toBitVec = s.regs.rbp.toBitVec
  r12 : t.1.regs.r12.toBitVec = s.regs.r12.toBitVec
  r13 : t.1.regs.r13.toBitVec = s.regs.r13.toBitVec
  r14 : t.1.regs.r14.toBitVec = s.regs.r14.toBitVec
  r15 : t.1.regs.r15.toBitVec = s.regs.r15.toBitVec
  vector : t.1.zmms = s.zmms
  length : widthLoad t.1.dmem s.regs.rdi.toNat 8 = some written
  status : Mem.loadInt t.1.dmem (s.regs.rdi.toBitVec + 64) 4 = some 0
  output : OutputAt s.dmem t.1.dmem s.regs.r8.toBitVec s.regs.r9.toNat
    (SszNative.CodecEmit.emit desc value supplied ⟨s.regs.r8.toNat, s.regs.r9.toNat⟩).writes
  frame : SszX86.Codec.MemoryFrame s.dmem t.1.dmem (Writable s desc written)

end SszX86.CodecEmit

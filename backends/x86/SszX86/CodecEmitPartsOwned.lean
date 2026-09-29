import SszX86.CodecEmitOwned
import SszX86.CodecEmitPartsInvariant
import SszX86.BitVectorMappingClosure

set_option autoImplicit false

namespace SszX86.CodecEmitParts
open SszNative UintCodec

/-- The Parts call is entered after the enclosing emitter's 152-byte activation
and the actual eight-byte return-address push. -/
def stackBytes (desc : SszNative.Codec.Desc) : Nat := CodecEmit.stackBytes desc - 160

def Writable (s : MachineData) (desc : SszNative.Codec.Desc) (written : Nat)
    (a : BitVec 64) : Prop :=
  Emit.InSpan a s.regs.r9.toBitVec written ∨
  Emit.InSpan a s.regs.rdi.toBitVec 8 ∨
  Emit.InSpan a (s.regs.rdi.toBitVec + 64) 4 ∨
  SszX86.Codec.StackWrites s.regs.rsp.toBitVec (stackBytes desc) a

/-- The seven-argument private ABI has output in R9 and capacity in the incoming
stack argument. Plans and immutable Parts may alias any other readonly input. -/
structure Owned (s : MachineData) (rootBase : Int64) (desc : SszNative.Codec.Desc)
    (parts : CodecMeasure.Parts) (values : List SszNative.Codec.Value)
    (supplied : Option CodecMeasure.Plan) (capacity : Nat)
    (r : SszX86.Codec.Footprint) (ra : BitVec 64) where
  composite : SszNative.CodecEmit.Composite desc parts
  call : CodecEmit.GeneratedCall desc (.seq values) supplied capacity
  physical : ∀ value, value ∈ values → value.Physical
  partsStored : PartsAt s.dmem r s.regs.rsi.toBitVec parts
  valuesStored : SszX86.Codec.ValuesAt s.dmem r s.regs.rdx.toBitVec values
  count : s.regs.rcx.toNat = values.length
  plansStored : OptionPlanAt s.dmem r s.regs.r8.toBitVec supplied
  capacityStored : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8) 8 = some (capacity : Int)
  outputBound : s.regs.r9.toNat + capacity ≤ 2 ^ 64
  resultBound : s.regs.rdi.toNat + 72 ≤ 2 ^ 64
  returnBound : s.regs.rsp.toNat + 16 ≤ 2 ^ 64
  stack : SszX86.Codec.StackAt s.dmem s.regs.rsp.toBitVec (stackBytes desc)
  outputMapped : Large.Mapped s.dmem s.regs.r9.toBitVec call.measured.size.value
  lengthMapped : Large.Mapped s.dmem s.regs.rdi.toBitVec 8
  statusMapped : Large.Mapped s.dmem (s.regs.rdi.toBitVec + 64) 4
  returnSlot : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))
  outputResult : Large.Disjoint s.regs.r9.toBitVec s.regs.rdi.toBitVec capacity 72
  outputStack : Large.Disjoint s.regs.r9.toBitVec
    (s.regs.rsp.toBitVec - BitVec.ofNat 64 (stackBytes desc)) capacity (stackBytes desc + 16)
  resultStack : Large.Disjoint s.regs.rdi.toBitVec
    (s.regs.rsp.toBitVec - BitVec.ofNat 64 (stackBytes desc)) 72 (stackBytes desc + 16)
  readonly : ∀ a, r a → ¬ Writable s desc call.measured.size.value a
  table : CodecEmit.TableAt s.dmem rootBase
  partsTable : CodecEmit.Table1At s.dmem rootBase
  classifierTable : CodecIsFixed.TableAt s.dmem (rootBase + 2800)
  tableReadonly : ∀ a, Emit.InSpan a (CodecEmit.tableAddress rootBase) 16 →
    ¬ Writable s desc call.measured.size.value a
  partsTableReadonly : ∀ a, Emit.InSpan a (CodecEmit.table1Address rootBase) 20 →
    ¬ Writable s desc call.measured.size.value a
  classifierTableReadonly : ∀ a,
    Emit.InSpan a (CodecIsFixed.tableAddress (rootBase + 2800)) 48 →
    ¬ Writable s desc call.measured.size.value a

def writes (parts : CodecMeasure.Parts) (values : List SszNative.Codec.Value)
    (supplied : Option CodecMeasure.Plan) (out capacity : Nat) :
    List SszNative.CodecEmit.Write :=
  (SszNative.CodecEmit.emitParts parts values
    (fun value _ desc plan target => SszNative.CodecEmit.emit desc value plan target)
    supplied ⟨out, capacity⟩).writes

structure Post (s : MachineData) (desc : SszNative.Codec.Desc)
    (parts : CodecMeasure.Parts) (values : List SszNative.Codec.Value)
    (supplied : Option CodecMeasure.Plan) (capacity : Nat)
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
  output : CodecEmit.OutputAt s.dmem t.1.dmem s.regs.r9.toBitVec capacity
    (writes parts values supplied s.regs.r9.toNat capacity)
  frame : SszX86.Codec.MemoryFrame s.dmem t.1.dmem (Writable s desc written)

/-- Recursive emit calls consume the actual 200-byte Parts activation plus their
return address. Strict declaration descent supplies the reusable child stack. -/
theorem child_stack_bound (desc child : SszNative.Codec.Desc)
    (member : child ∈ desc.children) :
    208 + CodecEmit.stackBytes child ≤ stackBytes desc := by
  have smaller := SszNative.Codec.Desc.child_nesting_lt desc child member
  have demand := SszX86.Codec.recursiveStackBytes_child
    (desc.nesting + 1) (child.nesting + 1) 160 368 (by omega) (by decide)
  unfold stackBytes CodecEmit.stackBytes SszX86.Codec.descriptorStackBytes
  omega

/-- Stack re-use follows actual instruction semantics, even inside the opaque
callee stack write frame. This is a consequence of a proved execution, not an
additional recursive assumption or public input premise. -/
theorem execution_retains_mapping (e : Executable) (s : MachineState)
    (P : MachineState → Prop) (run : Eventually (step e) P s) :
    Eventually (step e) (fun t => P t ∧ BitVector.Mapping.Extends s.1.dmem t.1.dmem) s :=
  BitVector.Mapping.retains_mapping e P s run

end SszX86.CodecEmitParts

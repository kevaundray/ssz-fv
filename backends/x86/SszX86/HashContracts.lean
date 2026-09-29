import SszX86.HashCompression
import SszX86.HashDecode
import SszX86.NatMulMemsetEmbedded

namespace SszX86.Hash

/-- The wrapper and every directly used implementation at their real link offsets. -/
structure LinkedCode (e : Executable) (root : Int64) : Prop where
  finalize : Finalize.CodeAt e (root - 256)
  combine : Combine.CodeAt e root
  compress : Compress.CodeAt e (root - 912)
  memcpy : Emit.MemcpyCodeAt e (root + 127872)
  memset : NatMul.MemsetCall.MemsetCodeAt e (root + 127936)

def FinalizeWritable (s : MachineData) (a : BitVec 64) : Prop :=
  InSpan a s.regs.rdi.toBitVec 32 ∨ InSpan a s.regs.rsi.toBitVec 112 ∨
  InSpan a (s.regs.rsp.toBitVec - 192) 192

/-- Initial ownership of the consumed state, output, deepest stack, and constants. -/
structure FinalizePre (root : Int64) (s : MachineData) (state : Model)
    (ra : BitVec 64) : Prop where
  state : StateAt s.dmem s.regs.rsi.toBitVec state
  output : Mapped s.dmem s.regs.rdi.toBitVec 32
  stack : StackAt s.dmem s.regs.rsp.toBitVec 192
  returnSlot : ReturnAt s ra
  statePhysical : Physical s.regs.rsi.toBitVec 112
  outputPhysical : Physical s.regs.rdi.toBitVec 32
  stateOutput : Disjoint s.regs.rsi.toBitVec s.regs.rdi.toBitVec 112 32
  stackState : Disjoint (s.regs.rsp.toBitVec - 192) s.regs.rsi.toBitVec 200 112
  stackOutput : Disjoint (s.regs.rsp.toBitVec - 192) s.regs.rdi.toBitVec 200 32
  tables : TablesAt s.dmem root
  tablePhysical : TablesPhysical root
  tablesState : TablesDisjoint root s.regs.rsi.toBitVec 112
  tablesOutput : TablesDisjoint root s.regs.rdi.toBitVec 32
  tablesStack : TablesDisjoint root (s.regs.rsp.toBitVec - 192) 192

structure FinalizePost (s : MachineData) (state : Model) (ra : BitVec 64)
    (t : MachineState) : Prop where
  returned : Returned s ra t
  digest : BytesAt t.1.dmem s.regs.rdi.toBitVec
    (SszNative.HashStream.finalize state).data.toList
  frame : MemoryFrame s.dmem t.1.dmem (FinalizeWritable s)
  stack : StackAt t.1.dmem s.regs.rsp.toBitVec 192

def CombineWritable (s : MachineData) (a : BitVec 64) : Prop :=
  InSpan a s.regs.rdi.toBitVec 32 ∨ InSpan a (s.regs.rsp.toBitVec - 368) 368

/-- Sources are independent read-only borrows: they may alias each other. -/
structure CombinePre (root : Int64) (s : MachineData) (left right : ByteArray)
    (ra : BitVec 64) : Prop where
  leftLength : s.regs.rdx.toNat = left.size
  rightLength : s.regs.r8.toNat = right.size
  leftPhysical : Physical s.regs.rsi.toBitVec left.size
  rightPhysical : Physical s.regs.rcx.toBitVec right.size
  outputPhysical : Physical s.regs.rdi.toBitVec 32
  output : Mapped s.dmem s.regs.rdi.toBitVec 32
  stack : StackAt s.dmem s.regs.rsp.toBitVec 368
  returnSlot : ReturnAt s ra
  leftOutput : Disjoint s.regs.rsi.toBitVec s.regs.rdi.toBitVec left.size 32
  rightOutput : Disjoint s.regs.rcx.toBitVec s.regs.rdi.toBitVec right.size 32
  leftStack : Disjoint s.regs.rsi.toBitVec (s.regs.rsp.toBitVec - 368) left.size 368
  rightStack : Disjoint s.regs.rcx.toBitVec (s.regs.rsp.toBitVec - 368) right.size 368
  stackOutput : Disjoint (s.regs.rsp.toBitVec - 368) s.regs.rdi.toBitVec 376 32
  tables : TablesAt s.dmem root
  tablePhysical : TablesPhysical root
  tablesOutput : TablesDisjoint root s.regs.rdi.toBitVec 32
  tablesStack : TablesDisjoint root (s.regs.rsp.toBitVec - 368) 368
  left : BytesAt s.dmem s.regs.rsi.toBitVec left.data.toList
  right : BytesAt s.dmem s.regs.rcx.toBitVec right.data.toList

structure CombinePost (s : MachineData) (left right : ByteArray) (ra : BitVec 64)
    (t : MachineState) : Prop where
  returned : Returned s ra t
  digest : BytesAt t.1.dmem s.regs.rdi.toBitVec
    (SszNative.HashStream.combine left right).data.toList
  left : BytesAt t.1.dmem s.regs.rsi.toBitVec left.data.toList
  right : BytesAt t.1.dmem s.regs.rcx.toBitVec right.data.toList
  frame : MemoryFrame s.dmem t.1.dmem (CombineWritable s)
  stack : StackAt t.1.dmem s.regs.rsp.toBitVec 368

end SszX86.Hash

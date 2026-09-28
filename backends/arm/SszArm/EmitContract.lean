import SszArm.EmitImpl
import SszArm.NatDivisionMemory

namespace SszArm.Emit

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value)
open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame)

structure Args where
  result : BitVec 64
  descriptor : BitVec 64
  value : BitVec 64
  output : BitVec 64
  capacity : BitVec 64
  stack : BitVec 64

def Args.ofEntry (s : ArmState) : Args :=
  ⟨r (.GPR 0#5) s, r (.GPR 1#5) s, r (.GPR 2#5) s,
   r (.GPR 4#5) s, r (.GPR 5#5) s, r (.GPR 31#5) s⟩

def Args.bodySP (args : Args) : BitVec 64 := args.stack - 160#64

def descriptorTag : Desc → BitVec 64
  | .bool => 0 | .uint _ => 1 | .byteVector _ => 2 | .byteList _ => 3
  | .bitVector _ => 4 | .bitList _ => 5 | .progressiveBitList _ => 6

def descriptorBytes : Desc → Nat
  | .bool => 8 | .progressiveBitList _ => 32 | _ => 24

def valueTag : Value → BitVec 8
  | .bool _ => 0 | .uint _ => 1 | .bytes _ => 2 | .bits _ => 3
  | .seq _ => 4 | .union _ _ => 5

def valueBytes : Value → Nat
  | .bool _ => 2 | .uint _ | .bytes _ => 24 | .bits _ => 48 | _ => 1

def descriptorOperands : Desc → List NatOperand
  | .bool => []
  | .uint operand | .byteVector operand | .byteList operand
  | .bitVector operand | .bitList operand => [operand]
  | .progressiveBitList none => []
  | .progressiveBitList (some operand) => [operand]

def valueOperands : Value → List NatOperand
  | .uint operand => [operand] | _ => []

def DescriptorAt (s : ArmState) (address : BitVec 64) (desc : Desc) : Prop :=
  read_mem_bytes 8 address s = descriptorTag desc ∧
  match desc with
  | .bool => True
  | .uint operand | .byteVector operand | .byteList operand
  | .bitVector operand | .bitList operand =>
    SszNative.NatArithmetic.operandAt (widthLoad s) (address.toNat + 8) operand
  | .progressiveBitList none => read_mem_bytes 8 (address + 8#64) s = 0#64
  | .progressiveBitList (some operand) =>
    read_mem_bytes 8 (address + 8#64) s = 1#64 ∧
    SszNative.NatArithmetic.operandAt (widthLoad s) (address.toNat + 16) operand

def ValueAt (s : ArmState) (address : BitVec 64) (value : Value) : Prop :=
  read_mem_bytes 1 address s = valueTag value ∧
  match value with
  | .bool flag => read_mem_bytes 1 (address + 1#64) s = if flag then 1#8 else 0#8
  | .uint number => SszNative.NatArithmetic.operandAt (widthLoad s) (address.toNat + 8) number
  | .bytes bytes =>
    (read_mem_bytes 8 (address + 16#64) s).toNat = bytes.size ∧
    (read_mem_bytes 8 (address + 8#64) s).toNat + bytes.size ≤ 2^64 ∧
    SszNative.ByteView.BytesAt (widthLoad s)
      (read_mem_bytes 8 (address + 8#64) s).toNat bytes
  | .bits bits =>
    (read_mem_bytes 8 (address + 24#64) s).toNat = bits.bytes.size ∧
    (read_mem_bytes 8 (address + 16#64) s).toNat + bits.bytes.size ≤ 2^64 ∧
    SszNative.ByteView.BytesAt (widthLoad s)
      (read_mem_bytes 8 (address + 16#64) s).toNat bits.bytes ∧
    read_mem_bytes 8 (address + 32#64) s = bits.count.setWidth 64 ∧
    read_mem_bytes 8 (address + 40#64) s = (bits.count >>> 64).setWidth 64
  | .seq _ | .union _ _ => True

def backingSpan (s : ArmState) (args : Args) : Value → List Span
  | .bytes bytes => [((read_mem_bytes 8 (args.value + 8#64) s).toNat, bytes.size)]
  | .bits bits => [((read_mem_bytes 8 (args.value + 16#64) s).toNat, bits.bytes.size)]
  | _ => []

/-- Only actual save stores and actual below-SP lowering stores are writable.
The unused 80-byte middle of the 160-byte activation is not writable. -/
def stackWrites (args : Args) : List Span :=
  [(args.stack.toNat - 176, 16), (args.stack.toNat - 80, 80)]

def bodyWrites (args : Args) (size : Nat) : List Span :=
  [(args.stack.toNat - 176, 16), (args.result.toNat, 8)] ++
    (if size = 0 then [] else [(args.output.toNat, size)])

def writesFor (args : Args) (size : Nat) : List Span :=
  stackWrites args ++ [(args.result.toNat, 8), (args.result.toNat + 64, 4)] ++
    (if size = 0 then [] else [(args.output.toNat, size)])

/-- Geometry and original borrowed observations only: no Plan storage, future
state, computed branch, helper exit, output initialization, or logical width cap. -/
structure Owned (s : ArmState) (args : Args) (desc : Desc) (value : Value) (size : Nat) : Prop where
  expected : SszNative.Serialize.expectedSize desc value = .ok size
  representable : size < 2^64
  fitting : size ≤ args.capacity.toNat
  physical : value.Physical
  descriptorBound : args.descriptor.toNat + descriptorBytes desc ≤ 2^64
  descriptor : DescriptorAt s args.descriptor desc
  valueBound : args.value.toNat + valueBytes value ≤ 2^64
  value_at : ValueAt s args.value value
  resultBound : args.result.toNat + 68 ≤ 2^64
  outputBound : args.output.toNat + args.capacity.toNat ≤ 2^64
  stackLow : 176 ≤ args.stack.toNat
  resultStack : Protected (stackWrites args) args.result.toNat 68
  outputStack : Protected (stackWrites args) args.output.toNat args.capacity.toNat
  outputResult : Protected [(args.result.toNat, 8), (args.result.toNat + 64, 4)]
    args.output.toNat args.capacity.toNat
  descriptorOwned : Protected (writesFor args size) args.descriptor.toNat (descriptorBytes desc)
  valueOwned : Protected (writesFor args size) args.value.toNat (valueBytes value)
  operandOwned : ∀ operand ∈ descriptorOperands desc ++ valueOperands value,
    NatDivision.OperandOwned (writesFor args size) operand
  backingOwned : ∀ span ∈ backingSpan s args value,
    Protected (writesFor args size) span.1 span.2

/-- The four callee-saved working arguments before any primitive body executes. -/
structure BodyRegisters (s : ArmState) (args : Args) : Prop where
  result : r (.GPR 19#5) s = args.result
  output : r (.GPR 20#5) s = args.output
  capacity : r (.GPR 21#5) s = args.capacity
  value : r (.GPR 22#5) s = args.value
  stack : r (.GPR 31#5) s = args.bodySP

/-- A primitive body stops at the shared success-status store, before the real
restore/RET. Its exact result length and bytes contain no old-output reads. -/
structure Produced (s t : ArmState) (args : Args) (desc : Desc) (value : Value) (size : Nat)
    (base : BitVec 64) : Prop where
  pc : read_pc t = base + 1004#64
  program : t.program = s.program
  error : read_err t = .None
  resultRegister : r (.GPR 19#5) t = args.result
  stack : r (.GPR 31#5) t = args.bodySP
  length : read_mem_bytes 8 args.result t = BitVec.ofNat 64 size
  bytes : SszNative.ByteView.BytesAt (widthLoad t) args.output.toNat
    (SszNative.Serialize.emit desc value)
  frame : MemoryFrame (bodyWrites args size) s t
  registers : ∀ reg : BitVec 5, reg ∈ [18#5, 28#5, 29#5] → r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64

structure Returned (s t : ArmState) : Prop where
  pc : read_pc t = r (.GPR 30#5) s
  error : read_err t = .None
  program : t.program = s.program
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  registers : ∀ reg : BitVec 5, 18 ≤ reg.toNat → reg.toNat ≤ 30 →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64

structure Post (s t : ArmState) (desc : Desc) (value : Value) (size : Nat) : Prop where
  returned : Returned s t
  length : read_mem_bytes 8 (Args.ofEntry s).result t = BitVec.ofNat 64 size
  status : read_mem_bytes 4 ((Args.ofEntry s).result + 64#64) t = 0#32
  bytes : SszNative.ByteView.BytesAt (widthLoad t) (Args.ofEntry s).output.toNat
    (SszNative.Serialize.emit desc value)
  frame : MemoryFrame (writesFor (Args.ofEntry s) size) s t
  descriptor : DescriptorAt t (Args.ofEntry s).descriptor desc
  value_at : ValueAt t (Args.ofEntry s).value value
  descriptorBytes : read_mem_bytes (descriptorBytes desc) (Args.ofEntry s).descriptor t =
    read_mem_bytes (descriptorBytes desc) (Args.ofEntry s).descriptor s
  valueBytes : read_mem_bytes (valueBytes value) (Args.ofEntry s).value t =
    read_mem_bytes (valueBytes value) (Args.ofEntry s).value s
  operands : ∀ operand ∈ descriptorOperands desc ++ valueOperands value,
    NatDivision.OperandPreserved s t operand
  backing : ∀ span ∈ backingSpan s (Args.ofEntry s) value, ∀ a : BitVec 64,
    span.1 ≤ a.toNat → a.toNat < span.1 + span.2 → t.mem a = s.mem a
  tail : ∀ index, size ≤ index → index < (Args.ofEntry s).capacity.toNat →
    t.mem ((Args.ofEntry s).output + BitVec.ofNat 64 index) =
      s.mem ((Args.ofEntry s).output + BitVec.ofNat 64 index)

end SszArm.Emit

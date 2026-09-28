import SszArm.NatToU128Exec
import SszArm.NatDivisionMemory
import SszNatNarrow

namespace SszArm.NatToU128

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame Returned)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The result is 32 bytes; its Option discriminant occupies the first sixteen.
The lowering uses exactly sixteen bytes below the original stack pointer. -/
def localWrites (s : ArmState) : List Span :=
  [((r (.GPR 0#5) s).toNat, 32), ((r (.GPR 31#5) s).toNat - 16, 16)]

/-- None leaves the complete payload untouched. -/
def writesFor (s : ArmState) (operand : SszNative.NatOperand) : List Span :=
  [((r (.GPR 0#5) s).toNat,
      if (SszNative.NatNarrow.toU128 operand).isSome then 32 else 16),
   ((r (.GPR 31#5) s).toNat - 16, 16)]

/-- Only physically valid caller storage and the original representation are
assumed. In particular high zero padding and empty Large operands are allowed. -/
structure Owned (s : ArmState) (operand : SszNative.NatOperand) : Prop where
  operandPointer : r (.GPR 1#5) s = operand.pointer
  operandPayload : r (.GPR 2#5) s = operand.payload
  operandAt : operand.At (widthLoad s)
  outputBound : (r (.GPR 0#5) s).toNat + 32 ≤ 2^64
  stackBound : 16 ≤ (r (.GPR 31#5) s).toNat
  outputStack : Protected [((r (.GPR 31#5) s).toNat - 16, 16)]
    (r (.GPR 0#5) s).toNat 32
  operandOwned : NatDivision.OperandOwned (localWrites s) operand

structure Post (s t : ArmState) (operand : SszNative.NatOperand) : Prop where
  returned : Returned s t
  result : SszNative.NatNarrow.U128ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
    (SszNative.NatNarrow.toU128 operand)
  frame : MemoryFrame (writesFor s operand) s t
  input : NatDivision.OperandPreserved s t operand

/-- The discriminant-and-payload relation is equivalent to representability,
without a canonicality or significant-width premise. -/
theorem Post.some_value {s t : ArmState} {operand : SszNative.NatOperand}
    (post : Post s t operand) (value : BitVec 128)
    (equal : value.toNat = operand.value) :
    SszNative.NatNarrow.U128ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat (some value) := by
  have result := (SszNative.NatNarrow.toU128_some_iff operand value).2 equal
  simpa only [result] using post.result

theorem Post.none_value {s t : ArmState} {operand : SszNative.NatOperand}
    (post : Post s t operand) (large : 2^128 ≤ operand.value) :
    SszNative.NatNarrow.U128ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat none := by
  have result := (SszNative.NatNarrow.toU128_none_iff operand).2 large
  simpa only [result] using post.result

end SszArm.NatToU128

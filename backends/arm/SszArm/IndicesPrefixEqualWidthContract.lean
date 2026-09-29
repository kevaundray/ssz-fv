import SszArm.IndicesPrefixEqualContract
import SszArm.IndicesPrefixEqualReturn
import SszArm.IndicesPrefixEqualClzWord
import SszArm.IndicesPrefixEqualSubtract
import SszIndicesArithmeticSemanticCore

namespace SszArm.Indices.PrefixEqual.Width

open SszNative (NatOperand)
open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame)
open Udivti3 (join)

/-- The original comparator's width-comparison cut, before instruction 432.
The stack argument is still readonly; both saturating differences retain their
full u128 range. This is an internal observation, not an entry precondition. -/
structure Ready (original current : ArmState) (base : BitVec 64)
    (left : NatOperand) (leftShift : BitVec 128) (flip : Bool)
    (right : NatOperand) (rightShift : BitVec 128) : Prop where
  pc : read_pc current = base + 432#64
  program : current.program = original.program
  error : read_err current = .None
  aligned : CheckSPAlignment current
  memory : MemoryFrame (writes original) original current
  saved : Return.Saved original current
  leftPointer : r (.GPR 0#5) current = left.pointer
  leftPayload : r (.GPR 1#5) current = left.payload
  leftLow : r (.GPR 2#5) current = leftShift.setWidth 64
  leftHigh : r (.GPR 3#5) current = (leftShift >>> 64).setWidth 64
  flipArgument : (r (.GPR 4#5) current).setWidth 32 = if flip then 1#32 else 0#32
  rightPointer : r (.GPR 5#5) current = right.pointer
  rightPayload : r (.GPR 6#5) current = right.payload
  rightLow : r (.GPR 10#5) current = rightShift.setWidth 64
  rightHigh : r (.GPR 11#5) current = (rightShift >>> 64).setWidth 64
  leftWidth : join (r (.GPR 9#5) current) (r (.GPR 8#5) current) =
    SszNative.Indices.bitLength left - leftShift.toNat
  rightWidth : join (r (.GPR 12#5) current) (r (.GPR 13#5) current) =
    SszNative.Indices.bitLength right - rightShift.toNat
  leftAt : left.At (widthLoad current)
  rightAt : right.At (widthLoad current)
  rightShiftAt :
    (Codec.Storage.Image.word (r (.GPR 31#5) original).toNat 8 (rightShift.setWidth 64).toNat ⋏
      Codec.Storage.Image.word ((r (.GPR 31#5) original).toNat + 8) 8
        ((rightShift >>> 64).setWidth 64).toNat).Owned (writes original) current

end SszArm.Indices.PrefixEqual.Width

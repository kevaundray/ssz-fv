import SszArm.IndicesStorage
import SszArm.IndicesLinkedPrefixEqual
import SszIndicesCore

namespace SszArm.Indices.PrefixEqual

open SszNative (NatOperand)
open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame)

/-- The comparator has no arena argument and never reserves storage. Its only
mutable region is the sixteen-byte save pair and the sixteen-byte lowering
slot immediately below it. Caller-provided rightShift remains above entry SP. -/
def writes (s : ArmState) : List Span :=
  [((r (.GPR 31#5) s).toNat - 32, 32)]

/-- Original machine-entry observations. Nat pairs are passed in registers, so
there is no invented in-memory Nat header. Neither readonly input is required
to be disjoint from the other. Both shifts retain all 128 supplied bits. -/
structure Owned (s : ArmState) (left : NatOperand) (leftShift : BitVec 128) (flip : Bool)
    (right : NatOperand) (rightShift : BitVec 128) : Prop where
  stack : Codec.Storage.Physical ((r (.GPR 31#5) s).toNat - 32) 32 16
  stackLower : 32 ≤ (r (.GPR 31#5) s).toNat
  leftPointer : r (.GPR 0#5) s = left.pointer
  leftPayload : r (.GPR 1#5) s = left.payload
  leftLow : r (.GPR 2#5) s = leftShift.setWidth 64
  leftHigh : r (.GPR 3#5) s = (leftShift >>> 64).setWidth 64
  flipArgument : (r (.GPR 4#5) s).setWidth 32 = if flip then 1#32 else 0#32
  rightPointer : r (.GPR 5#5) s = right.pointer
  rightPayload : r (.GPR 6#5) s = right.payload
  rightShiftAt :
    (Codec.Storage.Image.word (r (.GPR 31#5) s).toNat 8 (rightShift.setWidth 64).toNat ⋏
      Codec.Storage.Image.word ((r (.GPR 31#5) s).toNat + 8) 8
        ((rightShift >>> 64).setWidth 64).toNat).Owned (writes s) s
  leftAt : left.At (widthLoad s)
  rightAt : right.At (widthLoad s)
  leftBacking : Codec.Storage.Backing (Protected (writes s)) left
  rightBacking : Codec.Storage.Backing (Protected (writes s)) right

/-- The public observation is the exact width-first operational comparator,
including the zero-width flip case. No numeric-xor domain restriction is added. -/
structure Post (s t : ArmState) (left : NatOperand) (leftShift : BitVec 128) (flip : Bool)
    (right : NatOperand) (rightShift : BitVec 128) : Prop where
  returned : Delimited.Returned s t
  value : (r (.GPR 0#5) t).setWidth 32 =
    if SszNative.Indices.prefixEqual left leftShift.toNat flip right rightShift.toNat then 1#32 else 0#32
  memory : MemoryFrame (writes s) s t
  program : t.program = s.program

theorem backing_owned (writes : List Span) (operand : NatOperand)
    (backing : Codec.Storage.Backing (Protected writes) operand) :
    NatDivision.OperandOwned writes operand := by
  cases operand with
  | small value => trivial
  | large pointer words => exact backing.2

theorem Post.left_preserved {s t : ArmState} {left right : NatOperand}
    {leftShift rightShift : BitVec 128} {flip : Bool}
    (owned : Owned s left leftShift flip right rightShift)
    (post : Post s t left leftShift flip right rightShift) : left.At (widthLoad t) :=
  NatDivision.operand_at_preserved post.memory left owned.leftAt
    (backing_owned _ left owned.leftBacking)

theorem Post.right_preserved {s t : ArmState} {left right : NatOperand}
    {leftShift rightShift : BitVec 128} {flip : Bool}
    (owned : Owned s left leftShift flip right rightShift)
    (post : Post s t left leftShift flip right rightShift) : right.At (widthLoad t) :=
  NatDivision.operand_at_preserved post.memory right owned.rightAt
    (backing_owned _ right owned.rightBacking)

/-- Arena state is merely an optional readonly observation of the caller;
it is unchanged without requiring an arena, allocation, or future-run premise. -/
theorem Post.read_preserved {s t : ArmState} {left right : NatOperand}
    {leftShift rightShift : BitVec 128} {flip : Bool}
    (post : Post s t left leftShift flip right rightShift)
    (address bytes : Nat) (physical : address + bytes ≤ 2^64)
    (protected : Protected (writes s) address bytes) :
    widthLoad t address bytes = widthLoad s address bytes :=
  post.memory.load address bytes physical protected

end SszArm.Indices.PrefixEqual

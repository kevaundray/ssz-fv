import SszArm.CodecDecodeNatCmpOrder

namespace SszArm.Codec.Decode.NatCmpUsize

open UintCodec (widthLoad)
open SszNative

def localWrites (s : ArmState) : List Delimited.Span :=
  [((r (.GPR 31#5) s).toNat - 16, 16)]

/-- No logical Nat bound or canonicality condition occurs here. Only the
physical borrowed representation is protected from the descending-scan spill. -/
structure Owned (s : ArmState) (operand : NatOperand) : Prop where
  operandPointer : r (.GPR 0#5) s = operand.pointer
  operandPayload : r (.GPR 1#5) s = operand.payload
  operandAt : operand.At (widthLoad s)
  stackBound : 16 ≤ (r (.GPR 31#5) s).toNat
  operandOwned : NatDivision.OperandOwned (localWrites s) operand

theorem Owned.large_source {s : ArmState} {pointer : BitVec 64}
    {words : List (BitVec 64)} (owned : Owned s (.large pointer words)) :
    NatCompare.Source s pointer words :=
  NatNarrow.large_source s pointer words (localWrites s) owned.operandAt
    owned.operandOwned (by simp [localWrites]) owned.stackBound

theorem Owned.large_words {s : ArmState} {pointer : BitVec 64}
    {words : List (BitVec 64)} (owned : Owned s (.large pointer words)) :
    NatCompare.Words s pointer words := NatNarrow.large_words s pointer words owned.operandAt

theorem Frame.code {s t : ArmState} (frame : Frame s t) {base : BitVec 64}
    (code : CodeAt s base) : CodeAt t base := by
  simpa only [CodeAt, Linked.NatCmpUsize.CodeAt, Linked.WordsAt, frame.program] using code

theorem Frame.aligned {s t : ArmState} (frame : Frame s t)
    (aligned : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, frame.sp] using aligned

theorem Frame.memoryFrame {s t : ArmState} (frame : Frame s t)
    (low : 16 ≤ (r (.GPR 31#5) s).toNat) : Delimited.MemoryFrame (localWrites s) s t := by
  intro address outside
  have apart := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [localWrites])
  apply frame.memory
  rcases apart with before | after
  · exact Or.inl before
  · right; omega

structure Post (s t : ArmState) (operand : NatOperand) : Prop where
  frame : Frame s t
  pc : read_pc t = r (.GPR 30#5) s
  error : read_err t = .None
  result : (r (.GPR 0#5) t).setWidth 8 = NatABI.orderingByte
    (compare operand.value (r (.GPR 2#5) s).toNat)
  input : operand.At (widthLoad t)

end SszArm.Codec.Decode.NatCmpUsize

import SszArm.NatExactExec
import SszArm.NatDivisionMemory
import SszNatNarrow

namespace SszArm.NatExact

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame Returned)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- This private Result has its status at byte 64, unlike the outer codec
Result's byte 72. Lowering spills sixteen bytes below the original SP. -/
def localWrites (s : ArmState) : List Span :=
  [((r (.GPR 0#5) s).toNat, 68), ((r (.GPR 31#5) s).toNat - 16, 16)]

/-- Success writes only the 32-bit status. Failure writes its complete error. -/
def writesFor (s : ArmState) (expected : SszNative.NatOperand) : List Span :=
  [(if SszNative.NatNarrow.runExact expected (r (.GPR 2#5) s)
      then ((r (.GPR 0#5) s).toNat + 64, 4)
      else ((r (.GPR 0#5) s).toNat, 68)),
   ((r (.GPR 31#5) s).toNat - 16, 16)]

/-- X0 is the explicit output pointer, X1 points to the original Nat pair,
and X2 carries the actual usize. All immutable input bytes are protected. -/
structure Owned (s : ArmState) (expected : SszNative.NatOperand) : Prop where
  expectedAt : SszNative.NatArithmetic.operandAt (widthLoad s)
    (r (.GPR 1#5) s).toNat expected
  expectedBound : (r (.GPR 1#5) s).toNat + 16 ≤ 2^64
  expectedOwned : Protected (localWrites s) (r (.GPR 1#5) s).toNat 16
  operandOwned : NatDivision.OperandOwned (localWrites s) expected
  outputBound : (r (.GPR 0#5) s).toNat + 68 ≤ 2^64
  stackBound : 16 ≤ (r (.GPR 31#5) s).toNat
  outputStack : Protected [((r (.GPR 31#5) s).toNat - 16, 16)]
    (r (.GPR 0#5) s).toNat 68

structure Post (s t : ArmState) (expected : SszNative.NatOperand) : Prop where
  returned : Returned s t
  result : SszNative.NatNarrow.ExactResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
    expected (r (.GPR 2#5) s)
  frame : MemoryFrame (writesFor s expected) s t
  input : NatDivision.OperandPreserved s t expected
  expectedAt : SszNative.NatArithmetic.operandAt (widthLoad t)
    (r (.GPR 1#5) s).toNat expected
  expectedBytes : ∀ a : BitVec 64, (r (.GPR 1#5) s).toNat ≤ a.toNat →
    a.toNat < (r (.GPR 1#5) s).toNat + 16 → t.mem a = s.mem a

theorem Post.success {s t : ArmState} {expected : SszNative.NatOperand}
    (post : Post s t expected) (equal : expected.value = (r (.GPR 2#5) s).toNat) :
    widthLoad t ((r (.GPR 0#5) s).toNat + 64) 4 = some 0 := by
  have accepted := (SszNative.NatNarrow.runExact_iff expected (r (.GPR 2#5) s)).2 equal
  simpa only [SszNative.NatNarrow.ExactResultAt, accepted, ↓reduceIte] using post.result

end SszArm.NatExact

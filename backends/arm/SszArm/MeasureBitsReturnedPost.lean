import SszArm.MeasureBitsPropagationError
import SszArm.MeasureResultFields
import SszArm.BitVectorPair

namespace SszArm.Measure.Bits

open UintCodec (widthLoad)

structure ReturnedPost (s t : ArmState) (base : BitVec 64)
    (result : Except SszNative.Serialize.Error SszNative.NatOperand)
    (writes : List Delimited.Span) : Prop where
  pc : read_pc t = base + 4116#64
  program : t.program = s.program
  error : read_err t = .None
  stack : r (.GPR 31#5) t = r (.GPR 31#5) s
  result : ResultAt (widthLoad t) (r (.GPR 19#5) s).toNat result
  frame : Delimited.MemoryFrame writes s t
  registers : ∀ reg : BitVec 5, reg ∈ [18#5, 27#5, 28#5, 29#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64

end SszArm.Measure.Bits

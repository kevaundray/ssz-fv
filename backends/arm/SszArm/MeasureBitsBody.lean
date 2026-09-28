import SszArm.MeasureBitsListBody

namespace SszArm.Measure.Bits

open SszNative (NatOperand)
open SszNative.Serialize (Value)

theorem bitList_body (s : ArmState) (args : Args) (cap : NatOperand) (value : Value)
    (base : BitVec 64) (owned : Owned s args (.bitList cap) value)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1248#64) (registers : BodyRegisters s args)
    (descriptor : r (.GPR 1#5) s = args.descriptor)
    (tag : r (.GPR 8#5) s = (Emit.valueTag value).setWidth 64) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args (.bitList cap) value base :=
  List.body_executes (.bounded cap) s args value base owned code error aligned pc registers descriptor tag

theorem progressiveBitList_body (s : ArmState) (args : Args) (cap : Option NatOperand) (value : Value)
    (base : BitVec 64) (owned : Owned s args (.progressiveBitList cap) value)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 684#64) (registers : BodyRegisters s args)
    (descriptor : r (.GPR 1#5) s = args.descriptor)
    (tag : r (.GPR 8#5) s = (Emit.valueTag value).setWidth 64) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args (.progressiveBitList cap) value base :=
  List.body_executes (.progressive cap) s args value base owned code error aligned pc registers descriptor tag

end SszArm.Measure.Bits

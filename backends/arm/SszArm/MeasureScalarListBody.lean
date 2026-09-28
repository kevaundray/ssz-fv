import SszArm.MeasureScalarListReady

namespace SszArm.Measure

open SszNative (NatOperand)
open SszNative.Serialize (Value)

theorem byteList_body (s : ArmState) (base : BitVec 64) (args : Args)
    (cap : NatOperand) (value : Value)
    (owned : Owned s args (.byteList cap) value) (registers : BodyRegisters s args)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 776#64) (descriptor : r (.GPR 1#5) s = args.descriptor)
    (tag : r (.GPR 8#5) s = (Emit.valueTag value).setWidth 64) :
    ∃ fuel t, run fuel s = t ∧ Produced s t args (.byteList cap) value base := by
  cases value with
  | bytes bytes =>
    exact Scalar.Bytes.list_bytes_body s base args cap bytes owned registers code error aligned pc
      descriptor (by simp [tag, Emit.valueTag])
  | bool flag | uint flag | bits flag | seq flag =>
    exact Scalar.Bytes.wrong_entry_body .list s base args cap _ owned registers code error aligned pc
      (by simp [tag, Emit.valueTag]) (by rfl)
  | union selector content =>
    exact Scalar.Bytes.wrong_entry_body .list s base args cap _ owned registers code error aligned pc
      (by simp [tag, Emit.valueTag]) (by rfl)

end SszArm.Measure

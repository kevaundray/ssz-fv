import SszArm.EmitScalarBool
import SszArm.EmitScalarBytes

namespace SszArm.Emit

open SszNative (NatOperand)

theorem byteVector_body (s : ArmState) (base : BitVec 64) (args : Args)
    (length : NatOperand) (bytes : Ssz.Bytes) (size : Nat)
    (owned : Owned s args (.byteVector length) (.bytes bytes) size)
    (registers : BodyRegisters s args) (code : CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 820#64)
    (tag : r (.GPR 8#5) s = descriptorTag (.byteVector length)) :
    ∃ steps t, run steps s = t ∧ Produced s t args (.byteVector length) (.bytes bytes) size base :=
  Scalar.bytes_body s base args (.byteVector length) bytes size ⟨length, Or.inl rfl⟩
    owned registers code error aligned pc tag

theorem byteList_body (s : ArmState) (base : BitVec 64) (args : Args)
    (limit : NatOperand) (bytes : Ssz.Bytes) (size : Nat)
    (owned : Owned s args (.byteList limit) (.bytes bytes) size)
    (registers : BodyRegisters s args) (code : CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 820#64)
    (tag : r (.GPR 8#5) s = descriptorTag (.byteList limit)) :
    ∃ steps t, run steps s = t ∧ Produced s t args (.byteList limit) (.bytes bytes) size base :=
  Scalar.bytes_body s base args (.byteList limit) bytes size ⟨limit, Or.inr rfl⟩
    owned registers code error aligned pc tag

end SszArm.Emit

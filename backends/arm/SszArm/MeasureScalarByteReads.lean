import SszArm.MeasureScalarByteFacts

namespace SszArm.Measure.Scalar.Bytes

open SszNative (NatOperand)
open UintCodec (widthLoad)

theorem cap_reads {kind : Kind} {s : ArmState} {args : Args} {cap : NatOperand} {bytes : Ssz.Bytes}
    (owned : Owned s args (kind.desc cap) (.bytes bytes)) :
    read_mem_bytes 8 (args.descriptor + 8#64) s = cap.pointer ∧
      read_mem_bytes 8 (args.descriptor + 16#64) s = cap.payload := by
  have header : SszNative.NatArithmetic.operandAt (widthLoad s) (args.descriptor.toNat + 8) cap := by
    cases kind <;> exact owned.descriptor.2
  constructor
  · apply BitVec.eq_of_toNat_eq
    have value := Option.some.inj header.1
    simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using value
  · apply BitVec.eq_of_toNat_eq
    have value := Option.some.inj header.2.1
    simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.add_assoc] using value

theorem length_read {kind : Kind} {s : ArmState} {args : Args} {cap : NatOperand} {bytes : Ssz.Bytes}
    (owned : Owned s args (kind.desc cap) (.bytes bytes)) :
    read_mem_bytes 8 (args.value + 16#64) s = BitVec.ofNat 64 bytes.size := by
  apply BitVec.eq_of_toNat_eq
  have physical : bytes.size < 2^64 := owned.physical
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt physical] using owned.value_at.2.1

end SszArm.Measure.Scalar.Bytes

import SszArm.BitVectorStageState
import SszArm.BitVectorPair
import SszArm.BitVectorCopySpace

namespace SszArm.BitVector

open UintCodec (widthLoad)

private theorem copied_expected {s c : ArmState} {length expected : SszNative.NatOperand}
    {data : Ssz.Bytes} (owned : Owned s length data) (sourceOffset : Nat)
    (pair : SszNative.NatArithmetic.operandAt (widthLoad c)
      (r (.GPR 31#5) s + BitVec.ofNat 64 sourceOffset).toNat expected)
    (limbs : NatDivision.OperandOwned (localWrites s) expected) :
    SszNative.NatArithmetic.operandAt
      (widthLoad (write_mem_bytes 16 (r (.GPR 31#5) s + 48#64)
        (read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 (sourceOffset + 8)) c ++
          read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 sourceOffset) c) c))
      (r (.GPR 31#5) s + 48#64).toNat expected := by
  have pointer : read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 sourceOffset) c =
      expected.pointer := by
    simpa only [BitVec.add_zero] using read_of_observe_offset c
      (r (.GPR 31#5) s + BitVec.ofNat 64 sourceOffset) 0 8 expected.pointer
      (by simpa only [Nat.add_zero] using pair.1)
  have payload : read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 (sourceOffset + 8)) c =
      expected.payload := by
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using read_of_observe_offset c
      (r (.GPR 31#5) s + BitVec.ofNat 64 sourceOffset) 8 8 expected.payload pair.2.1
  rw [pointer, payload]
  have bound := owned.stackHigh
  exact operand_at_written_pair c _ expected (by bv_omega) pair.2.2
    ((stack_copy_covered owned 48 16 (by decide)).operand expected limbs)

theorem division_expected_pair {s c : ArmState} {base : BitVec 64}
    {length expected : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (current : Working s c length)
    (pair : SszNative.NatArithmetic.operandAt (widthLoad c)
      (r (.GPR 31#5) s + 64#64).toNat expected)
    (limbs : NatDivision.OperandOwned (localWrites s) expected) :
    SszNative.NatArithmetic.operandAt (widthLoad (ExpectedStage.Stage.division.result c base))
      (r (.GPR 31#5) s + 48#64).toNat expected := by
  have copied := copied_expected owned 64 pair limbs
  have observe : widthLoad (ExpectedStage.Stage.division.result c base) =
      widthLoad (write_mem_bytes 16 (r (.GPR 31#5) s + 48#64)
        (read_mem_bytes 8 (r (.GPR 31#5) s + 72#64) c ++
          read_mem_bytes 8 (r (.GPR 31#5) s + 64#64) c) c) := by
    funext address bytes
    simp only [widthLoad, ExpectedStage.Stage.result, state_simp_rules, current.sp]
  rw [observe]
  exact copied

theorem rounded_expected_pair {s c : ArmState} {base : BitVec 64}
    {length expected : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (current : Working s c length)
    (pair : SszNative.NatArithmetic.operandAt (widthLoad c)
      (r (.GPR 31#5) s + 144#64).toNat expected)
    (limbs : NatDivision.OperandOwned (localWrites s) expected) :
    SszNative.NatArithmetic.operandAt (widthLoad (ExpectedStage.Stage.rounded.result c base))
      (r (.GPR 31#5) s + 48#64).toNat expected := by
  have copied := copied_expected owned 144 pair limbs
  have observe : widthLoad (ExpectedStage.Stage.rounded.result c base) =
      widthLoad (write_mem_bytes 16 (r (.GPR 31#5) s + 48#64)
        (read_mem_bytes 8 (r (.GPR 31#5) s + 152#64) c ++
          read_mem_bytes 8 (r (.GPR 31#5) s + 144#64) c) c) := by
    funext address bytes
    simp only [widthLoad, ExpectedStage.Stage.result, state_simp_rules, current.sp]
  rw [observe]
  exact copied

theorem division_expected_pc {s c : ArmState} {base : BitVec 64}
    {length : SszNative.NatOperand} {remainder : BitVec 64}
    (current : Counted s c length remainder) :
    read_pc (ExpectedStage.Stage.division.result c base) =
      if remainder = 0#64 then base + 5948#64 else base + 3392#64 := by
  simp only [ExpectedStage.Stage.result, state_simp_rules, current.remainderValue]
  rfl

end SszArm.BitVector

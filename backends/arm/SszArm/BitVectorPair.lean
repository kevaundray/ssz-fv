import SszArm.BitVectorFrame

namespace SszArm.BitVector

open UintCodec (widthLoad)

/-- Interpret a shared absolute-address observation at the actual architectural
pointer. This conversion itself does not impose a spurious alignment premise. -/
theorem read_of_observe_offset (s : ArmState) (pointer : BitVec 64) (offset bytes : Nat)
    (value : BitVec (bytes * 8))
    (observed : widthLoad s (pointer.toNat + offset) bytes = some value.toNat) :
    read_mem_bytes bytes (pointer + BitVec.ofNat 64 offset) s = value := by
  apply BitVec.eq_of_toNat_eq
  simpa only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    Option.some.injEq] using observed

theorem observe_of_read_offset (s : ArmState) (pointer : BitVec 64) (offset bytes : Nat)
    (value : BitVec (bytes * 8))
    (loaded : read_mem_bytes bytes (pointer + BitVec.ofNat 64 offset) s = value) :
    widthLoad s (pointer.toNat + offset) bytes = some value.toNat := by
  simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, loaded]

theorem read_pair_written_low (s : ArmState) (target high low : BitVec 64)
    (physical : target.toNat + 16 ≤ 2^64) :
    read_mem_bytes 8 target (write_mem_bytes 16 target (high ++ low) s) = low := by
  rw [← BoolCodec.pair_read_low,
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 16 target (high ++ low) physical]
  exact BitVec.extractLsb'_append_right _ _

theorem read_pair_written_high (s : ArmState) (target high low : BitVec 64)
    (physical : target.toNat + 16 ≤ 2^64) :
    read_mem_bytes 8 (target + 8#64) (write_mem_bytes 16 target (high ++ low) s) = high := by
  rw [← BoolCodec.pair_read_high,
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 16 target (high ++ low) physical]
  exact BitVec.extractLsb'_append_left _ _

/-- The copied expected pair retains its original Large representation and all
referenced limbs, even when those limbs were allocated by the previous helper. -/
theorem operand_at_written_pair (s : ArmState) (target : BitVec 64)
    (operand : SszNative.NatOperand) (physical : target.toNat + 16 ≤ 2^64)
    (input : operand.At (widthLoad s))
    (separate : NatDivision.OperandOwned [(target.toNat, 16)] operand) :
    SszNative.NatArithmetic.operandAt
      (widthLoad (write_mem_bytes 16 target (operand.payload ++ operand.pointer) s))
      target.toNat operand := by
  refine ⟨?_, ?_, ?_⟩
  · have low := read_pair_written_low s target operand.payload operand.pointer physical
    simp only [widthLoad, BitVec.ofNat_toNat, BitVec.setWidth_eq, low]
  · simpa only [Nat.add_zero] using observe_of_read_offset
      (write_mem_bytes 16 target (operand.payload ++ operand.pointer) s) target 8 8
      operand.payload (read_pair_written_high s target operand.payload operand.pointer physical)
  · exact NatDivision.operand_at_preserved
      (Delimited.store_frame s target 16 (operand.payload ++ operand.pointer) physical)
      operand input separate

end SszArm.BitVector

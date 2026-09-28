import ProofAudit
import SszDivision
import SszDivisionBits
import SszLimbs
import SszPackedBits
import SszFixed
import SszWordDecode
import SszCursor
import SszLimbOrder
import SszBool
import SszUint
import SszArena
import SszByteView
import SszNatABI
import SszBitView
import SszDelimitedProofs
import SszNatAdd
import SszNatDivision
import SszNatArithmeticMemory
import SszNatOperandNormalization
import SszNatAddMemory
import SszNatDivisionMemory
import SszNatNarrow
import SszBitVector
import SszBitVectorMemory
import SszSerializeResources
import SszArm.EmitImpl
import SszArm.MeasureImpl
import SszArm.NatFromU128Model
import SszArm.LogicalImmediateRegression
import SszArm.Impl
import SszArm.Proofs
import SszArm.SszBridge
import SszArm.MemcpyProofs
import SszArm.MemsetProofs
import SszArm.MemcmpProofs
import SszArm.MemmoveProofs
import SszArm.Udivti3Proofs
import SszArm.BytesCodec
import SszArm.BoolStores
import SszArm.BoolReturn
import SszArm.BoolActivation
import SszArm.UintLarge
import SszArm.UintBodyMemory
import SszArm.UintPrefixCompletion
import SszArm.UintBody
import SszArm.ByteViewBody
import SszArm.ByteViewControlFlow
import SszArm.NatCompareProofs
import SszArm.DelimitedProofs
import SszArm.NatDivisionProofs
import SszArm.NatToU128Proofs
import SszArm.NatExactProofs
import SszArm.NatAddProofs
import SszArm.BitVectorProgram
import SszArm.BitVectorProofs
import SszArm.BitListProofs
import SszArm.DispatchProofs
import SszArm.BoolProofs
import SszArm.BoolBody
import SszArm.BoolBlockMemory
import SszArm.UintPrefix
import SszWidth
import SszArm.UintAllocation
import SszArm.UintTails

-- Inspect the transitive proof dependencies, not just the local source text.
#print axioms SszArm.loadProgram_run
#print axioms SszArm.storeProgram_run
#print axioms SszArm.loadProgram_correct
#print axioms SszArm.storeProgram_correct
#print axioms SszArm.memoryBytes_eq_uintBytes
#print axioms SszArm.storeProgram_ssz
#print axioms SszArm.loadProgram_ssz
#print axioms SszArm.Memcpy.program_correct
#print axioms SszArm.Memcpy.program_zero
#print axioms SszArm.Memset.program_correct
#print axioms SszArm.Memset.program_zero
#print axioms SszArm.Memcmp.program_correct
#print axioms SszArm.Memcmp.program_zero
#print axioms SszArm.Memcmp.program_first_difference
#print axioms SszArm.Memmove.program_correct
#print axioms SszArm.Memmove.program_zero
#print axioms SszArm.Memmove.program_equal
#print axioms SszNative.Division.loop_quotient
#print axioms SszNative.Division.loop_remainder
#print axioms SszNative.DivisionBits.remainderStep_toNat
#print axioms SszArm.Udivti3.program_run
#print axioms SszArm.Udivti3.program_correct
#print axioms SszArm.Memcpy.program_ssz
#print axioms SszNative.Limbs.bytes_eq_uintBytes
#print axioms SszNative.Limbs.deserialize_uint
#print axioms SszNative.PackedBits.packBits_unpackBits_canonicalBytes
#print axioms SszNative.PackedBits.packBitsDelimited_unpackBits
#print axioms SszNative.PackedBits.deserialize_progressiveBitList
#print axioms SszNative.Fixed.classify_isFixed
#print axioms SszNative.Fixed.variable_width
#print axioms SszNative.Fixed.size_eq
#print axioms SszNative.WordDecode.packPrefix_toNat
#print axioms SszNative.WordDecode.deserialize_uint
#print axioms SszNative.WordDecode.decodeWords_length
#print axioms SszNative.WordDecode.outcome_eq_deserialize
#print axioms SszNative.UintCodec.result_refines
#print axioms SszNative.Cursor.writeCursor_spec
#print axioms SszNative.Cursor.writeCursor_assemble
#print axioms SszNative.Cursor.writeInline_assemble
#print axioms SszNative.Limbs.trim_eq_take
#print axioms SszNative.Limbs.nativeCmp_correct
#print axioms SszNative.BoolCodec.outcome_eq_deserialize
#print axioms SszNative.BoolCodec.result_refines
#print axioms SszArm.BoolCodec.all_decode
#print axioms SszArm.BoolCodec.step_at
#print axioms SszArm.BoolCodec.length_branch
#print axioms SszArm.BoolCodec.byte_zero_branch
#print axioms SszArm.BoolCodec.byte_one_branch
#print axioms SszArm.BoolCodec.error_tail
#print axioms SszArm.BoolCodec.epilogue
#print axioms SszArm.BoolCodec.jump_to
#print axioms SszArm.BoolCodec.returned_pc_of_activation
#print axioms SszArm.BoolCodec.aligned_sub32
#print axioms SszArm.BoolCodec.scope_stores_run
#print axioms SszArm.BoolCodec.bad_stores_run
#print axioms SszArm.BoolCodec.true_stores_run
#print axioms SszArm.BoolCodec.false_stores_run
#print axioms SszArm.BoolCodec.tag_stores_run
#print axioms SszArm.BoolCodec.scope_result
#print axioms SszArm.BoolCodec.bad_result
#print axioms SszArm.BoolCodec.success_result
#print axioms SszArm.BoolCodec.zeroPair_effect
#print axioms SszArm.BoolCodec.body_run
#print axioms SszArm.BoolCodec.body_frame
#print axioms SszArm.BoolCodec.body_return_pc
#print axioms SszArm.BoolCodec.body_refines
#print axioms SszArm.UintCodec.all_decode
#print axioms SszArm.UintCodec.bool_codeAt
#print axioms SszArm.UintCodec.memcpy_codeAt
#print axioms SszArm.UintCodec.width_branch
#print axioms SszArm.UintCodec.width_comparison
#print axioms SszArm.UintCodec.small_descriptor
#print axioms SszNative.Arena.success_properties
#print axioms SszNative.Arena.exhausted_iff
#print axioms SszNative.Arena.mask_rounding
#print axioms SszNative.Limbs.width_pair_eq
#print axioms SszArm.UintCodec.arena_step
#print axioms SszArm.UintCodec.arena_block_run
#print axioms SszArm.UintCodec.arena_runs
#print axioms SszNative.Arena.high_bit_clear
#print axioms SszArm.UintCodec.Small.trim_and_pack
#print axioms SszArm.UintCodec.arena_success
#print axioms SszArm.UintCodec.arena_failure
#print axioms SszArm.UintCodec.width_runs
#print axioms SszArm.UintCodec.width_cps
#print axioms SszArm.UintCodec.prefix_runs
#print axioms SszArm.UintCodec.allocation_runs
#print axioms SszArm.UintCodec.Tail.success_correct
#print axioms SszArm.UintCodec.Tail.scope_correct
#print axioms SszArm.UintCodec.Tail.scratch_exhausted_correct
#print axioms SszArm.UintCodec.Large.fill
#print axioms SszArm.UintCodec.Small.Stable.nat_pair
#print axioms SszArm.UintCodec.width_at_of_pair
#print axioms SszArm.UintCodec.Small.Stable.returned
#print axioms SszArm.UintCodec.prefix_finish_or_allocate
#print axioms SszArm.UintCodec.allocated_body_runs
#print axioms SszArm.UintCodec.Body.runs
#print axioms SszArm.UintCodec.Body.Result.refines
#print axioms SszNative.ByteView.vector_outcome_eq_deserialize
#print axioms SszNative.ByteView.list_outcome_eq_deserialize
#print axioms SszArm.ByteView.Vector.runs
#print axioms SszArm.ByteView.Bounded.runs
#print axioms SszArm.ByteView.Result.descriptor_at
#print axioms SszArm.ByteView.ControlFlow.boundsPanic_unreachable
#print axioms SszNative.NatMemory.Pair.at
#print axioms SszNative.NatMemory.pair_of_at
#print axioms SszNative.BitView.vector_outcome_eq_deserialize
#print axioms SszNative.BitView.list_outcome_eq_deserialize
#print axioms SszNative.BitView.progressive_outcome_eq_deserialize
#print axioms SszNative.BitView.highestBit_log2
#print axioms SszNative.BitView.rounded_byte_count
#print axioms SszNative.BitView.exact_scope_quotient_small
#print axioms SszNative.BitView.vector_count_bound
#print axioms SszNative.BitView.delimited_count_bound
#print axioms SszNative.BitView.delimited_count_large
#print axioms SszNative.BitView.delimited_unpack_retained
#print axioms SszArm.NatCompare.compare_correct
#print axioms SszNative.Delimited.run_bitList
#print axioms SszNative.Delimited.run_progressiveBitList
#print axioms SszNative.Delimited.run_scratch_iff
#print axioms SszNative.Delimited.run_resources
#print axioms SszNative.Delimited.result_refines
#print axioms SszNative.Delimited.PreparedAt.pair
#print axioms SszArm.Delimited.decode_correct
#print axioms SszArm.Delimited.Post.refines
#print axioms SszArm.Delimited.Post.bitList
#print axioms SszNative.NatAdd.run_value
#print axioms SszNative.NatAdd.allocation_geometry
#print axioms SszNative.NatDivision.run_success
#print axioms SszNative.NatDivision.run_badRepresentation_iff
#print axioms SszNative.NatArithmetic.operandAt.pair
#print axioms SszNative.NatOperand.normalized_at
#print axioms SszArm.LogicalImmediateRegression.actual_mov_arbitrary_state
#print axioms SszArm.LogicalImmediateRegression.orr_destination_sp
#print axioms SszArm.LogicalImmediateRegression.ands_destination_zr_flags
#print axioms SszNative.NatArithmetic.fromWide_result_at
#print axioms SszNative.NatAdd.run_result_at
#print axioms SszNative.NatDivision.run_result_at
#print axioms SszArm.NatDivision.program_correct
#print axioms SszArm.NatDivision.program_correct_success
#print axioms SszArm.NatToU128.to_u128_correct
#print axioms SszArm.NatExact.exact_correct
#print axioms SszArm.NatAdd.add_correct
#print axioms SszArm.NatAdd.add_correct_arithmetic

#print axioms SszNative.NatOperand.wordCount_le_iff_value_lt
#print axioms SszNative.NatNarrow.toU128_some_iff
#print axioms SszNative.NatNarrow.toU128_none_iff
#print axioms SszNative.NatNarrow.runExact_iff

#print axioms SszNative.BitVector.run_refines
#print axioms SszNative.BitVector.run_scratch_iff
#print axioms SszNative.BitVector.rounding_failure_no_rollback
#print axioms SszNative.BitVector.ResultAt.erased
#print axioms SszNative.BitVector.expected_of_division
#print axioms SszNative.BitVector.expected_of_round
#print axioms SszNative.BitVector.expected_remainder_bound
#print axioms SszNative.BitVector.scope_narrows
#print axioms SszArm.BitVector.run_program
#print axioms SszArm.BitVector.program_correct
#print axioms SszArm.BitVector.program_refines
#print axioms SszArm.BitList.program_correct
#print axioms SszArm.BitList.bitList_correct
#print axioms SszArm.BitList.progressiveBitList_correct
#print axioms SszArm.BitList.bitList_ssz_correct
#print axioms SszArm.BitList.progressiveBitList_ssz_correct
#print axioms SszArm.Dispatch.Boolean.program_correct
#print axioms SszArm.Dispatch.Bytes.program_correct
#print axioms SszArm.Dispatch.Bytes.program_refines
#print axioms SszArm.Dispatch.BitVector.program_correct
#print axioms SszArm.Dispatch.BitVector.program_refines
#print axioms SszArm.Dispatch.Unsigned.program_correct
#print axioms SszArm.Dispatch.Unsigned.program_refines
#print axioms SszArm.DispatchBitList.program_correct
#print axioms SszArm.DispatchBitList.bitList_ssz_correct
#print axioms SszArm.DispatchBitList.progressiveBitList_ssz_correct

#print axioms SszNative.Arena.reserveBytes_some_iff
#print axioms SszNative.Arena.reserveBytes_none_iff
#print axioms SszNative.Arena.reserveBytes_interval
#print axioms SszNative.Serialize.expected_encoding
#print axioms SszNative.Serialize.measure_refines
#print axioms SszNative.Serialize.encodedSize_refines
#print axioms SszNative.Serialize.serialize_refines
#print axioms SszNative.Serialize.serializeAlloc_refines
#print axioms SszNative.Serialize.serialize_success_iff
#print axioms SszNative.Serialize.serializeAlloc_success_iff
#print axioms SszNative.Serialize.serialize_scratch_iff
#print axioms SszNative.Serialize.serializeAlloc_scratch_iff
#print axioms SszNative.Serialize.encodedSize_output_iff
#print axioms SszNative.Serialize.serialize_output_iff
#print axioms SszNative.Serialize.serializeAlloc_output_iff
#print axioms SszNative.Serialize.serialize_resources
#print axioms SszNative.Serialize.measureList_limit_no_rollback
#print axioms SszNative.Serialize.measureList_second_failure_no_rollback
#print axioms SszNative.Serialize.serializeAlloc_reservation_failure
#print axioms SszNative.Serialize.serializeAlloc_zero
#print axioms SszNative.Serialize.applyWrites_prefix
#print axioms SszNative.Serialize.applyWrites_tail
#print axioms SszNative.Serialize.applyWrites_no_read
#print axioms SszNative.Serialize.serialize_failure_unchanged

#print axioms SszArm.NatFromU128.correct
#print axioms SszArm.NatFromU128.small_correct
#print axioms SszArm.NatFromU128.Post.value
#print axioms SszArm.NatFromU128.Post.pair
#print axioms SszArm.NatFromU128.Post.protected
#print axioms SszArm.NatFromU128.small_resources
#print axioms SszArm.NatFromU128.allocated_iff
#print axioms SszArm.NatFromU128.exhausted_iff
#print axioms SszArm.NatFromU128.Post.allocated
#print axioms SszArm.NatFromU128.Post.unallocated
#print axioms SszArm.NatFromU128.correct_value
#print axioms SszArm.NatFromU128.Post.result_owned
#print axioms SszArm.NatFromU128.correct_model

#print axioms SszNative.Serialize.bitLength_significant
#print axioms SszNative.Serialize.requiredBytes_significant
#print axioms SszNative.Serialize.requiredBytes_zero_significant
#print axioms SszNative.Serialize.requiredBytes_u128
#print axioms SszNative.Serialize.wide_width_bound
#print axioms SszNative.Serialize.bsr_certificate

#print axioms SszArm.Emit.body_codeAt
#print axioms SszArm.Emit.memcpy_codeAt

#print axioms SszArm.Measure.body_codeAt
#print axioms SszArm.Measure.compare_codeAt
#print axioms SszArm.Measure.fromU128_codeAt
#print axioms SszArm.Measure.memcpy_codeAt

audit_native

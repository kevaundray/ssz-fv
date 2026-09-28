import SszArm.MeasureBitVectorAllocation
import SszArm.MeasureBitVectorScopeFields
import SszArm.MeasureErrorWritersProduced
import SszArm.MeasureAllocationFrame

namespace SszArm.Measure.BitVector

open SszNative (NatOperand)
open SszNative.Serialize (Packed)
open Delimited (MemoryFrame Protected)
open UintCodec (widthLoad)

theorem allocated_scope_produced {s u : ArmState} (base : BitVec 64) (args : Args)
    (cap : NatOperand) (bits : Packed) (actual : NatOperand)
    (owned : Owned s args (.bitVector cap) (.bits bits))
    (output : r (.GPR 19#5) s = args.result) (stack : r (.GPR 31#5) s = args.bodySP)
    (arena : r (.GPR 20#5) s = args.arena) (descriptor : r (.GPR 1#5) s = args.descriptor + 8#64)
    (low : r (.GPR 8#5) s = bits.count.setWidth 64)
    (high : r (.GPR 9#5) s = (bits.count >>> 64).setWidth 64)
    (mismatch : cap.value ≠ bits.count.toNat) (error : read_err s = .None)
    (post : Bits.Alloc.ConstructorPost .scope s u base)
    (success : (Bits.Alloc.outcome .scope s).result = .ok actual) :
    Produced s (Scope.result u base) args (.bitVector cap) (.bits bits) base := by
  have callEq := alloc_call_eq s args bits arena low high
  have calls : (outcome s args (.bitVector cap) (.bits bits)).calls = [Bits.Alloc.outcome .scope s] := by
    rw [mismatch_calls s args cap bits mismatch, callEq]
  have failure : (outcome s args (.bitVector cap) (.bits bits)).result = .error (.scope cap actual) := by
    rw [mismatch_outcome s args cap bits mismatch, ← callEq, success]
  have prefixFrame : MemoryFrame (allocationWrites args (outcome s args (.bitVector cap) (.bits bits))) s u := by
    simpa only [alloc_writes_eq s args cap bits arena low high mismatch] using post.frame
  have fullFrame : MemoryFrame (writesFor args (outcome s args (.bitVector cap) (.bits bits))) s u :=
    prefixFrame.weaken (fun span member => List.mem_append.mpr (Or.inr member))
  have output' : r (.GPR 19#5) u = args.result :=
    (post.registers 19#5 (by decide)).trans output
  have stack' : r (.GPR 31#5) u = args.bodySP := post.sp.trans stack
  have descriptor' : r (.GPR 1#5) u = args.descriptor + 8#64 :=
    (post.registers 1#5 (by decide)).trans descriptor
  have space0 := Result.semantic_error_space owned output stack _ failure
    (mismatch_inline s args cap bits mismatch)
  have space : Result.ErrorSpace u := by
    constructor
    · simpa only [post.sp] using space0.stack
    · simpa only [post.registers 19#5 (by decide)] using space0.bound
    · simpa only [post.sp, post.registers 19#5 (by decide)] using space0.fields
  have sameWrites : Result.errorWrites u = Result.errorWrites s := by
    simp only [Result.errorWrites, post.sp, post.registers 19#5 (by decide)]
  have subsetLocal : ∀ span ∈ Result.errorWrites u,
      span ∈ localWrites args (outcome s args (.bitVector cap) (.bits bits)) := by
    intro span member
    exact error_writes_subset_local owned output stack mismatch _ failure span
      (by simpa only [sameWrites] using member)
  have free : Protected (Result.errorWrites u) ((arenaOf s args).base + (arenaOf s args).used)
      ((arenaOf s args).capacity - (arenaOf s args).used) := by
    rcases owned.freeLocal with empty | separate
    · exact Or.inl empty
    · exact Or.inr (fun span member => separate span (List.mem_append.mpr (Or.inl (subsetLocal span member))))
  have actualOwned := Helpers.fromWide_result_owned (Result.errorWrites u) (arenaOf s args)
    bits.count owned.storageBound free actual (by simpa only [callEq] using success)
  have expectedOwned := operand_owned_subset cap
    (owned.operandOwned cap (by simp [Emit.descriptorOperands, Emit.valueOperands])) (by
      intro span member
      exact List.mem_append.mpr (Or.inl (subsetLocal span member)))
  have expectedAt := NatDivision.operand_at_preserved fullFrame cap
    (owned.operand_at cap (by simp [Emit.descriptorOperands, Emit.valueOperands]))
    (owned.operandOwned cap (by simp [Emit.descriptorOperands, Emit.valueOperands]))
  have live : Emit.DescriptorAt u args.descriptor (.bitVector cap) := descriptor_preserved owned fullFrame
  have fields : SszNative.NatArithmetic.operandAt (widthLoad u) (args.descriptor.toNat + 8) cap := live.2
  have expectedPointer : read_mem_bytes 8 (r (.GPR 1#5) u) u = cap.pointer := by
    rw [descriptor']
    apply BitVec.eq_of_toNat_eq
    simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using Option.some.inj fields.1
  have expectedPayload : read_mem_bytes 8 (r (.GPR 1#5) u + 8#64) u = cap.payload := by
    rw [descriptor']
    apply BitVec.eq_of_toNat_eq
    simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.add_assoc] using
      Option.some.inj fields.2.1
  have actualResult : read_pc u = base + 3416#64 ∧ r (.GPR 10#5) u = actual.pointer ∧
      r (.GPR 8#5) u = actual.payload ∧ actual.At (widthLoad u) := by
    have nativeResult := post.result
    simp only [success, Bits.Alloc.Site.entry, Bits.Alloc.Site.pointerReg,
      Bits.Alloc.Site.countReg] at nativeResult
    with_unfolding_all exact nativeResult
  have resultAt := Scope.result_at u base space cap actual expectedPointer expectedPayload
    actualResult.2.1 actualResult.2.2.1 expectedAt actualResult.2.2.2 expectedOwned actualOwned
  have suffixFrame := Scope.result_frame u base space
  have localFrame := suffixFrame.weaken subsetLocal
  have r0 := Emit.frame_read_offset localFrame args.arena 24 0 8 owned.arenaBound owned.headerLocal (by decide)
  have r8 := Emit.frame_read_offset localFrame args.arena 24 8 8 owned.arenaBound owned.headerLocal (by decide)
  have r16 := Emit.frame_read_offset localFrame args.arena 24 16 8 owned.arenaBound owned.headerLocal (by decide)
  simp only [BitVec.add_zero] at r0
  refine ⟨Scope.result_pc u base, (Scope.result_program u base).trans post.program,
    (Scope.result_error u base).trans (post.error.trans error), (Scope.result_sp u base).trans stack',
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [output', failure] using resultAt
  · rw [r16]
    simpa only [arena, mismatch_used s args cap bits mismatch, ← callEq] using post.cursor
  · exact ⟨r0.trans (by simpa only [arena, Bits.Alloc.addressWord] using post.header.1),
      r8.trans (by simpa only [arena, Bits.Alloc.capacityWord] using post.header.2)⟩
  · intro call member
    have equal : call = Bits.Alloc.outcome .scope s := by simpa only [calls, List.mem_singleton] using member
    subst call
    intro reservation allocated index
    have inCalls : Bits.Alloc.outcome .scope s ∈ (outcome s args (.bitVector cap) (.bits bits)).calls := by
      simp only [calls, List.mem_singleton]
    have buffer := owned.allocation_protected _ inCalls reservation allocated
    have bufferProtected : Protected (Result.errorWrites u) reservation.pointer
        (8 * (Bits.Alloc.outcome .scope s).written.length) := by
      rcases buffer with empty | separate
      · exact Or.inl empty
      · exact Or.inr (fun span member => separate span (List.mem_append.mpr (Or.inl (subsetLocal span member))))
    have bounds := (resource_measure (arenaOf s args) (.bitVector cap) (.bits bits)).allocations
      _ inCalls reservation allocated
    have storage := owned.storageBound
    have physical : reservation.pointer + 8 * (Bits.Alloc.outcome .scope s).written.length ≤ 2^64 := by omega
    have within := index.isLt
    rw [suffixFrame.load _ 8 (by omega) (bufferProtected.subspan (8 * index.val) 8 (by omega))]
    exact post.written reservation allocated index
  · have first : MemoryFrame (bodyWrites args (outcome s args (.bitVector cap) (.bits bits))) s u :=
      prefixFrame.weaken (fun span member => List.mem_append.mpr (Or.inr member))
    apply first.trans (suffixFrame.weaken ?_)
    intro span member
    rw [sameWrites, local_error_writes owned.stackLow output stack mismatch _ failure] at member
    exact List.mem_append.mpr (Or.inl member)
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      exact (Scope.result_register u base _ (by decide) (by decide) (by decide) (by decide)).trans
        (post.registers _ (by decide))
  · intro reg low high
    rw [Scope.result_vector, post.vectors]

end SszArm.Measure.BitVector

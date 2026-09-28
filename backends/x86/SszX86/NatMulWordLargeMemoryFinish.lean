import SszX86.NatMulWordLargeMemoryResources
import SszX86.NatMulWordReturn
import SszNatOperandNormalization

namespace SszX86.NatMulWord
open SszNative UintCodec

theorem large_allocated_at (s : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned s operand factor address capacity used ra)
    (m : DataMem) (r : Arena.Reservation)
    (allocated : (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).allocation = some r)
    (written : NatMemory.wordsAt (widthLoad m) r.pointer
      (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written) :
    (NatOperand.large (BitVec.ofNat 64 r.pointer)
      (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written).At (widthLoad m) := by
  have bounds := allocation_bounds s operand factor address capacity used ra owned r allocated
  have pointer := allocated_pointer_nat s operand factor address capacity used ra owned r allocated
  simp only [NatOperand.At, pointer]
  exact ⟨bounds.1, bounds.2.1, bounds.2.2.2.2.2, written⟩

/-- The actual publication cut is Finished: normalization chooses exactly the
checked fromWords pair, retains the full allocation, and preserves the original
saved registers. No post-state operand ownership is an input to this theorem. -/
theorem large_finished (s : MachineData) (operand : NatOperand)
    (factor address capacity used ra : BitVec 64) (owned : Owned s operand factor address capacity used ra)
    (r : Arena.Reservation) (words : List (BitVec 64))
    (model : SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat =
      NatArithmetic.committed r words)
    (m : DataMem)
    (work : WorkFrame s m (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat))
    (written : NatMemory.wordsAt (widthLoad m) r.pointer words)
    (cursor : widthLoad m (s.regs.r8.toNat+16) 8 = some r.used)
    (t : MachineData)
    (memory : t.dmem = successMem m s.regs.rdi.toBitVec
      (NatOperand.fromWords (BitVec.ofNat 64 r.pointer) words).pointer
      (NatOperand.fromWords (BitVec.ofNat 64 r.pointer) words).payload)
    (sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec-64)
    (simd : t.zmms = s.zmms) : Finished s operand factor address capacity used t := by
  let result := NatOperand.fromWords (BitVec.ofNat 64 r.pointer) words
  have allocated : (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).allocation = some r := by
    rw [model]
    rfl
  have beforeWritten : NatMemory.wordsAt (widthLoad m) r.pointer
      (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written := by
    simpa only [model, NatArithmetic.committed] using written
  have publish := NatMul.success_publish_frame s m result.pointer result.payload result owned.output_bound
  have wordPublish : NatMul.PublishFrame s m (successMem m s.regs.rdi.toBitVec result.pointer result.payload)
      (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).result := by
    simpa only [model, NatArithmetic.committed] using publish
  have finalWork : WorkFrame s t.dmem
      (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat) := by
    rw [memory]
    exact work.publish wordPublish
  have afterWritten : NatMemory.wordsAt (widthLoad t.dmem) r.pointer
      (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written := by
    rw [memory]
    exact large_publish_written s operand factor address capacity used ra owned _ _ (.ok result)
      publish r allocated beforeWritten
  have resultAt : result.At (widthLoad t.dmem) := by
    have original := large_allocated_at s operand factor address capacity used ra owned t.dmem r allocated afterWritten
    have normalized := NatOperand.fromWords_at _ _ _ original
    simpa only [model, NatArithmetic.committed] using normalized
  refine ⟨?_, ?_, finalWork.to_frame owned.stack_low, ?_, sp, ?_, simd⟩
  · rw [model, memory]
    rw [memory] at resultAt
    have observed := NatAdd.success_reads m s.regs.rdi.toBitVec result.pointer result.payload
    exact ⟨⟨observed.1, observed.2.1, resultAt⟩, observed.2.2⟩
  · intro actual actualAllocated
    have same : actual = r := Option.some.inj (actualAllocated.symm.trans allocated)
    subst actual
    exact afterWritten
  · rw [memory, large_publish_cursor s operand factor address capacity used ra owned _ _ (.ok result) publish]
    simpa only [model, NatArithmetic.committed] using cursor
  · have saved := finalWork.saved owned
    have address : t.regs.rsp.toBitVec+16 = s.regs.rsp.toBitVec-48 := by
      rw [sp]
      bv_omega
    rw [address]
    exact saved

end SszX86.NatMulWord

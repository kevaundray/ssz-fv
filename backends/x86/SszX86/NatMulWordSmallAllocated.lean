import SszX86.NatMulWordSmallFrame
import SszX86.NatMulWordCommitSmall

namespace SszX86.NatMulWord
open SszNative UintCodec

private theorem allocated_return_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (operand : NatOperand) (factor address capacity used ra : BitVec 64)
    (owned : Owned s operand factor address capacity used ra)
    (nonzero : factor ≠ 0) (notone : factor ≠ 1) (small : operand.wordCount ≤ 1)
    (ready : WideReady s t (SszNative.NatMul.wordProduct operand factor))
    (large : ¬ (SszNative.NatMul.wordProduct operand factor).toNat < 2^64)
    (r : Arena.Reservation)
    (reserved : Arena.reserve address.toNat capacity.toNat used.toNat 2 = some r)
    (flags : StatusFlags) :
    Eventually (step e) (Post s operand factor address capacity used ra)
      (SmallReservation.Ready t address used flags, base + 580) := by
  have physical := wide_owned s operand factor address capacity used ra owned
    (SszNative.NatMul.wordProduct operand factor)
  have mappedPayload := NatFromU128.reserve_mapped _ _ address capacity used ra physical r reserved
  obtain ⟨checks, shape⟩ := (Arena.reserve_eq_some_iff_checks _ _ _ 2 (by decide) r).mp reserved
  have pointer : address + BitVec.ofNat 64 (Arena.start address.toNat used.toNat) =
      BitVec.ofNat 64 r.pointer := by
    rw [shape]
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have finish : BitVec.ofNat 64 (Arena.start address.toNat used.toNat + 16) = BitVec.ofNat 64 r.used := by
    rw [shape]
    rfl
  apply commit_small_cps e base hc (SmallReservation.Ready t address used flags)
  · exact ⟨_, (ready.toPureFrame.header owned).used_load⟩
  · simpa only [SmallReservation.Ready, UInt64.toBitVec_ofBitVec, UInt64.toBitVec_ofNat',
      pointer, wideBase, ready.memory] using mappedPayload
  apply small_allocated_publish_cps e base hc
  · change Large.Mapped (commitMem t.dmem t.regs.r8.toBitVec
        (address + BitVec.ofNat 64 (Arena.start address.toNat used.toNat))
        (BitVec.ofNat 64 (Arena.start address.toNat used.toNat + 16))
        t.regs.rax.toBitVec t.regs.rdx.toBitVec) t.regs.rdi.toBitVec 72
    unfold commitMem NatFromU128.commitMem
    repeat' first | exact ready.toPureFrame.output_mapped owned | apply Large.mapped_store
  apply small_memory_finish_cps e base hc s _ operand factor address capacity used ra owned nonzero notone small
  · simp only [smallCommitted, SmallReservation.Ready, successMem, UInt64.toBitVec_ofBitVec,
      UInt64.toBitVec_ofNat', pointer, finish, ready.memory, ready.output, ready.arena, ready.low, ready.high,
      smallResultMem, NatFromU128.resultMem, wideBase, large, ↓reduceIte, reserved,
      NatFromU128.successMem]
  · simpa only [smallCommitted, SmallReservation.Ready] using ready.sp
  · exact ready.simd

/-- Exhaustive unsigned reservation followed by the original error or success
stores and the original stack-restoring RET. No reservation-success premise. -/
theorem small_reservation_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (operand : NatOperand) (factor address capacity used ra : BitVec 64)
    (owned : Owned s operand factor address capacity used ra)
    (nonzero : factor ≠ 0) (notone : factor ≠ 1) (small : operand.wordCount ≤ 1)
    (ready : WideReady s t (SszNative.NatMul.wordProduct operand factor))
    (large : ¬ (SszNative.NatMul.wordProduct operand factor).toNat < 2^64) :
    Eventually (step e) (Post s operand factor address capacity used ra) (t, base + 527) := by
  refine eventually_trans (step e) (SmallReservation.Post t base address capacity used)
    (Post s operand factor address capacity used ra) (t, base+527)
    (SmallReservation.runs e base hc t address capacity used (ready.toPureFrame.header owned)) ?_
  intro u result
  rcases u with ⟨u, pc⟩
  obtain ⟨frame, failure | success⟩ := result
  · obtain ⟨failed, pcEq⟩ := failure
    dsimp only at pcEq
    rw [pcEq]
    have physical : WideReady s u (SszNative.NatMul.wordProduct operand factor) := ready.after_reserve frame
    apply error_cps e base hc u (physical.toPureFrame.output_mapped owned)
    apply small_memory_finish_cps e base hc s _ operand factor address capacity used ra owned nonzero notone small
    · simp only [smallResultMem, NatFromU128.resultMem, wideBase, large, ↓reduceIte, failed,
        physical.memory, physical.output, errorMem, NatFromU128.errorMem]
    · exact physical.sp
    · exact physical.simd
  · obtain ⟨r, reserved, pcEq, flags, stateEq⟩ := success
    dsimp only at pcEq stateEq
    rw [pcEq, stateEq]
    exact allocated_return_cps e base hc s t operand factor address capacity used ra owned
      nonzero notone small ready large r reserved flags

end SszX86.NatMulWord

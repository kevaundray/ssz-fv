import SszArm.NatMulLargeEntry
import SszArm.NatMulLargeHeader

namespace SszArm.NatMul

open Delimited (Protected MemoryFrame)
open SszNative (NatOperand NatArithmetic)
open UintCodec (widthLoad)

theorem large_success_return (s u v : ArmState) (base : BitVec 64)
    (left right : NatOperand) (owned : Owned s left right)
    (start : LargeStart s u base left right)
    (largeLeft : 1 < left.wordCount) (largeRight : 1 < right.wordCount)
    (reservation : SszNative.Arena.Reservation)
    (allocated : LargeReservation s left right reservation)
    (ready : ReserveReady u v base reservation (left.wordCount + right.wordCount))
    (memory : MemoryFrame [((r (.GPR 31#5) u).toNat - 16, 16),
      ((r (.GPR 5#5) u + 16#64).toNat, 8),
      (reservation.pointer, 8 * (left.wordCount + right.wordCount))] u v)
    (code : JointCodeAt s base) (aligned : CheckSPAlignment s) :
    ∃ fuel t, run fuel v = t ∧ Post s t left right := by
  have sp := ready.sp.trans start.frame.sp
  have workFrame := (allocated.reserve_cover owned start.frame).frame memory
  have prefix := (start.frame.memoryFor (outcome s left right)).trans
    (allocated.work_cover.frame workFrame)
  have saved := large_saved_frame owned start.frame.saved workFrame
    (allocated.work_saved owned start.frame.sp) ready.sp ready.x29
    (by
      intro reg low high
      rw [ready.vectors reg (by intro zero; simp [zero] at low)])
  have vCode : CodeAt v base := by
    simpa only [CodeAt, ready.program] using start.frame.code code.body
  have vAligned : CheckSPAlignment v := by
    simpa only [CheckSPAlignment, state_simp_rules, ready.sp] using start.frame.aligned aligned
  have loopCover := allocated.work_cover.trans (allocated.loop_cover owned sp ready.pointer)
  have loopOwned : LoopEntryOwned v left right (r (.GPR 5#5) s) := by
    refine ⟨allocated.loop_space owned sp ready.pointer,
      NatAdd.operand_at_preserved prefix left owned.leftAt owned.leftOwned,
      NatAdd.operand_at_preserved prefix right owned.rightAt owned.rightOwned,
      large_operand_cover loopCover left owned.leftOwned,
      large_operand_cover loopCover right owned.rightOwned,
      owned.arenaBound, allocated.loop_arena owned sp ready.pointer,
      ready.left.trans (start.raw.1.trans owned.leftPointer),
      ready.payload.trans (start.payload.trans owned.leftPayload),
      ready.right.trans (start.raw.2.2.1.trans owned.rightPointer),
      ready.leftCount.trans start.leftCount, ready.rightCount.trans start.rightCount, ?_, ?_⟩
    · rw [ready.rowNext, start.previous]
      change BitVec.ofNat 64 (right.wordCount - 1) + BitVec.ofNat 64 1 = _
      rw [← BitVec.ofNat_add]
      congr 1
      omega
    · rw [ready.rowEnd, start.leftCount, start.previous, ← BitVec.ofNat_add]
      congr 1
      omega
  obtain ⟨loopFuel, w, loopRun, loopReady⟩ := reservation_loop_runs u v base
    (r (.GPR 5#5) s) left right reservation vCode vAligned ready loopOwned largeLeft largeRight
  have loopWorkFrame := (allocated.loop_cover owned sp ready.pointer).frame loopReady.memory
  have savedW := large_saved_frame owned saved loopWorkFrame
    (allocated.work_saved owned sp) loopReady.stable.sp
    (loopReady.stable.registers 29#5 (by decide))
    (by intro reg low high; rw [loopReady.stable.vectors])
  have output : r (.GPR 24#5) w = r (.GPR 0#5) s :=
    loopReady.result.trans (ready.result.trans start.frame.output)
  have space : ReturnSpace w (r (.GPR 24#5) w) := by
    rw [output]
    exact ReturnSpace.of_owned owned savedW
  have resultPointer : r (.GPR 20#5) w = BitVec.ofNat 64 reservation.pointer := by
    rw [← loopReady.pointer, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have resultCount : r (.GPR 23#5) w =
      BitVec.ofNat 64 (SszNative.NatMul.writtenWords left right).length - 1#64 := by
    rw [SszNative.NatMul.writtenWords_length, loopReady.normalization]
    have plus : BitVec.ofNat 64 (left.wordCount + right.wordCount - 1) + 1#64 =
        BitVec.ofNat 64 (left.wordCount + right.wordCount) := by
      change BitVec.ofNat 64 (left.wordCount + right.wordCount - 1) + BitVec.ofNat 64 1 = _
      rw [← BitVec.ofNat_add]
      congr 1
      omega
    rw [← plus, BitVec.add_sub_cancel]
  have returnCover := large_return_cover owned savedW.sp (r (.GPR 24#5) w) output
    (NatOperand.fromWords (BitVec.ofNat 64 reservation.pointer) (SszNative.NatMul.writtenWords left right))
    (by rw [allocated.model]; rfl)
  have freshLocal : Protected (localWrites s (outcome s left right)) reservation.pointer
      (8 * (left.wordCount + right.wordCount)) := by
    rcases allocated.fresh with empty | separate
    · exact Or.inl empty
    · exact Or.inr (fun span member => separate span (List.mem_append_left _ member))
  have freshReturn : Protected (returnWrites w (r (.GPR 24#5) w)) reservation.pointer
      (8 * (SszNative.NatMul.writtenWords left right).length) := by
    rw [SszNative.NatMul.writtenWords_length]
    exact returnCover.protected freshLocal
  obtain ⟨returnFuel, t, returnRun, returned, image, written, tailFrame⟩ :=
    normalize_committed_return s w base reservation (SszNative.NatMul.writtenWords left right)
      (loopReady.stable.code vCode) loopReady.error (loopReady.stable.aligned vAligned)
      loopReady.pc savedW space resultPointer resultCount
      (by rw [SszNative.NatMul.writtenWords_length]; exact allocated.physical)
      allocated.nonnull allocated.aligned allocated.addressBound
      (loopReady.written reservation rfl) freshReturn
  have frame := prefix.trans ((allocated.work_cover.frame loopWorkFrame).trans
    (((large_local_cover s (outcome s left right)).trans returnCover).frame tailFrame))
  have cursorReturn := large_header_read owned tailFrame (returnCover.protected owned.arenaLocal) 16 (by decide)
  have cursor : read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) t = BitVec.ofNat 64 reservation.used := by
    rw [cursorReturn, loopReady.arenaCursor]
    simpa only [start.frame.arena] using ready.cursor
  have header := large_header16_read owned frame (allocated.header owned)
  refine ⟨loopFuel + returnFuel, t, ?_, ?_⟩
  · rw [run_plus, loopRun, returnRun]
  · refine ⟨returned, ?_, ?_, ?_, frame,
      NatAdd.operand_preserved frame left owned.leftAt owned.leftOwned,
      NatAdd.operand_preserved frame right owned.rightAt owned.rightOwned, ?_, ?_⟩
    · simpa only [allocated.model, output] using image
    · simpa only [allocated.model] using written
    · rw [cursor, allocated.model]
      simp only [NatArithmetic.committed, BitVec.toNat_ofNat, Nat.mod_eq_of_lt allocated.usedBound]
    · simpa only [BitVec.ofNat_zero, BitVec.add_zero] using header 0 (by decide)
    · exact header 8 (by decide)

end SszArm.NatMul

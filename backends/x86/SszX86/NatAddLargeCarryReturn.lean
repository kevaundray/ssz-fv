import SszX86.NatAddCarry
import SszX86.NatAddLargeCommitMemory
import SszX86.NatAddLargeResultReturn

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- A real successful large reservation feeds the actual scalar or paired
carry loops, final normalization, exact publication, restores and RET. -/
theorem large_carry_finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra)
    (frame : ControlFrame (pushedState s) t)
    (leftPointer : t.regs.rsi.toBitVec = left.pointer) (leftPayload : t.regs.rdx.toBitVec = left.payload)
    (rightPointer : t.regs.rcx.toBitVec = right.pointer) (rightPayload : t.regs.r8.toBitVec = right.payload)
    (leftNonzero : left.wordCount ≠ 0) (rightNonzero : right.wordCount ≠ 0)
    (wide : 2 ≤ SszNative.NatAdd.count left right)
    (count : t.regs.rax.toNat = SszNative.NatAdd.count left right)
    (r : Arena.Reservation) (flags : StatusFlags)
    (model : SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat =
      NatArithmetic.committed r (SszNative.NatAdd.writtenWords left right)) :
    Eventually (step e) (Post s left right address capacity used ra)
      (Reservation.Large.reservedState t address used flags,base+536) := by
  let u := Reservation.Large.reservedState t address used flags
  let dst := BitVec.ofNat 64 r.pointer
  have allocated : (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = some r := by
    rw [model]
    rfl
  have geometry := SszNative.NatAdd.allocation_geometry left right address.toNat capacity.toNat used.toNat r allocated
  have pointerNat := allocated_pointer_nat s left right address capacity used ra owned r allocated
  have resources := large_commit_resources s t left right address capacity used ra owned frame count r flags model
  change Eventually (step e) (Post s left right address capacity used ra) (u,base+536)
  refine carry_cps e base hc u left right dst resources.2.1 resources.2.2.1
    leftNonzero rightNonzero wide resources.2.2.2.2.1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (Post s left right address capacity used ra) ?_
  · simpa only [model, NatArithmetic.committed, SszNative.NatAdd.writtenWords_length] using
      allocated_operand_apart s left right left address capacity used ra owned owned.left_at owned.left_owned r allocated
  · simpa only [model, NatArithmetic.committed, SszNative.NatAdd.writtenWords_length] using
      allocated_operand_apart s left right right address capacity used ra owned owned.right_at owned.right_owned r allocated
  · have bound := (allocation_bounds s left right address capacity used ra owned r allocated).2.2.2.2.2
    simpa only [dst, pointerNat, model, NatArithmetic.committed, SszNative.NatAdd.writtenWords_length] using bound
  · simpa only [Carry.get, u, Reservation.Large.reservedState, Reg64s.get64] using leftPointer
  · simpa only [Carry.get, u, Reservation.Large.reservedState, Reg64s.get64] using leftPayload
  · simpa only [Carry.get, u, Reservation.Large.reservedState, Reg64s.get64] using rightPointer
  · simpa only [Carry.get, u, Reservation.Large.reservedState, Reg64s.get64] using rightPayload
  · change t.regs.rax.toBitVec = BitVec.ofNat 64 (SszNative.NatAdd.count left right)
    rw [← count]
    change t.regs.rax.toBitVec = BitVec.ofNat 64 t.regs.rax.toBitVec.toNat
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [Carry.get, u, Reservation.Large.reservedState, Reg64s.get64,
      UInt64.toBitVec_ofBitVec, dst, geometry.2.1]
  · simp only [Carry.get, u, Reservation.Large.reservedState, Reg64s.get64,
      UInt64.toBitVec_ofBitVec, dst, geometry.2.1]
  · intro _
    change (2305843009213693950 : UInt64).toBitVec = 2305843009213693950#64
    decide
  · intro v carried
    have buffer : ∀ a : BitVec 64, Body.Outside a.toNat r.pointer
        (8*(SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written.length) →
        v.dmem.get? a = u.dmem.get? a := by
      intro a outside
      apply carried.frame a
      simpa only [dst, pointerNat, model, NatArithmetic.committed,
        SszNative.NatAdd.writtenWords_length] using outside
    have finalWork := resources.1.buffer r allocated buffer
    have finalCursor := (cursor_after_buffer s left right address capacity used ra owned
      u.dmem v.dmem r allocated buffer).trans resources.2.2.2.1
    have finalOut : v.regs.rdi = s.regs.rdi := carried.out.trans frame.output
    have beforeMapped : Large.Mapped u.dmem s.regs.rdi.toBitVec 68 := by
      have hm := resources.2.2.2.2.2
      change Large.Mapped u.dmem t.regs.rdi.toBitVec 68 at hm
      have out : t.regs.rdi = s.regs.rdi := frame.output
      rwa [out] at hm
    have finalMapped : OutputMapped v := by
      change Large.Mapped v.dmem v.regs.rdi.toBitVec 68
      rw [finalOut]
      exact output_mapped_after_buffer s left right address capacity used ra owned
        u.dmem v.dmem r allocated beforeMapped buffer
    refine large_result_finish_cps e base hc s v left right address capacity used ra owned r model
      finalWork ?_ finalCursor ((congrArg UInt64.toBitVec carried.sp).trans frame.sp)
      finalOut (carried.simd.trans frame.original_simd) finalMapped carried.count carried.pointer ?_
    · simpa only [dst, pointerNat] using carried.written
    · simpa only [List.head?_eq_getElem?] using carried.first

end SszX86.NatAdd

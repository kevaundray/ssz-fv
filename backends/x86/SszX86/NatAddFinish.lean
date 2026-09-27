import SszX86.NatAddMemory
import SszX86.NatAddStack

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Memory observations established before the shared six-pop epilogue. -/
structure Finished (s : MachineData) (left right : NatOperand)
    (address capacity used ra : BitVec 64) (t : MachineData) : Prop where
  observed : NatArithmetic.AddResultAt (widthLoad t.dmem) s.regs.rdi.toNat
    (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).result
  written : ∀ r,
    (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = some r →
    NatMemory.wordsAt (widthLoad t.dmem) r.pointer
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written
  frame : Frame s t.dmem
    (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat)
  cursor : widthLoad t.dmem (s.regs.r9.toNat + 16) 8 =
    some (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).used
  left_at : left.At (widthLoad t.dmem)
  right_at : right.At (widthLoad t.dmem)
  sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 48
  saved : SavedAt t.dmem t.regs.rsp.toBitVec s
  simd : t.zmms = s.zmms
  returnSlot : Mem.loadInt t.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))

/-- Actual POPs and RET establish every SysV preservation clause. -/
theorem finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (finished : Finished s left right address capacity used ra t) :
    Eventually (step e) (Post s left right address capacity used ra) (t, base + 612) := by
  apply restore_cps e base hc t s finished.saved
  apply ret_runs e base hc (restoredState t s) ra
  · simpa only [restoredState, UInt64.toBitVec_ofBitVec, finished.sp,
      BitVec.sub_add_cancel] using finished.returnSlot
  · refine ⟨finished.observed, finished.written, ?_, finished.frame, finished.cursor,
      finished.left_at, finished.right_at⟩
    refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, finished.simd, finished.returnSlot⟩
    simp only [Delimited.retState, restoredState, UInt64.toBitVec_ofBitVec,
      finished.sp, BitVec.sub_add_cancel]

end SszX86.NatAdd

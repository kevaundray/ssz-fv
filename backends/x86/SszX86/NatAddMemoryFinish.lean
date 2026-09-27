import SszX86.NatAddFinish
import SszX86.NatAddWorkMemory

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- A branch's exact stores and work frame suffice for the complete return:
original inputs, saved words and return slot are derived, not assumed again. -/
theorem finish_memory_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (left right : NatOperand) (address capacity used ra : BitVec 64)
    (owned : Owned s left right address capacity used ra)
    (work : WorkFrame s t.dmem (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat))
    (observed : NatArithmetic.AddResultAt (widthLoad t.dmem) s.regs.rdi.toNat
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).result)
    (written : ∀ r,
      (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).allocation = some r →
      NatMemory.wordsAt (widthLoad t.dmem) r.pointer
        (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).written)
    (cursor : widthLoad t.dmem (s.regs.r9.toNat+16) 8 =
      some (SszNative.NatAdd.run left right address.toNat capacity.toNat used.toNat).used)
    (sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 48)
    (simd : t.zmms = s.zmms) :
    Eventually (step e) (Post s left right address capacity used ra) (t, base + 612) := by
  have frame := work.to_frame owned.stack_low
  apply finish_cps e base hc s t left right address capacity used ra
  refine ⟨observed, written, frame, cursor, ?_, ?_, sp, ?_, simd, work.return_slot owned⟩
  · exact operand_preserved s left right left address capacity used ra owned t.dmem frame
      owned.left_at owned.left_owned
  · exact operand_preserved s left right right address capacity used ra owned t.dmem frame
      owned.right_at owned.right_owned
  · rw [sp]
    exact work.saved owned

end SszX86.NatAdd

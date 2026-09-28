import SszX86.NatMulWordMemory
import SszX86.NatMulWordStack
import SszX86.NatMulWordOutput

namespace SszX86.NatMulWord
open SszNative UintCodec

/-- An internal cut after real publication, before ADD RSP/POPs/RET. Original
input and return-slot ownership are deliberately not assumed at this cut. -/
structure Finished (s : MachineData) (operand : NatOperand)
    (factor address capacity used : BitVec 64) (t : MachineData) : Prop where
  observed : NatArithmetic.AddResultAt (widthLoad t.dmem) s.regs.rdi.toNat
    (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).result
  written : ∀ r,
    (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).allocation = some r →
    NatMemory.wordsAt (widthLoad t.dmem) r.pointer
      (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).written
  frame : Frame s t.dmem
    (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat)
  cursor : widthLoad t.dmem (s.regs.r8.toNat + 16) 8 =
    some (SszNative.NatMul.runWord operand factor address.toNat capacity.toNat used.toNat).used
  sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 64
  saved : SavedAt t.dmem (t.regs.rsp.toBitVec + 16) s
  simd : t.zmms = s.zmms

/-- All preserved input bytes and the return slot follow from the initial
physical regions. The six original POPs and original RET establish the ABI. -/
theorem finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (operand : NatOperand) (factor address capacity used ra : BitVec 64)
    (owned : Owned s operand factor address capacity used ra)
    (finished : Finished s operand factor address capacity used t) :
    Eventually (step e) (Post s operand factor address capacity used ra) (t, base + 687) := by
  have returnSlot := finished.frame.return_slot owned
  have original := operand_preserved s operand factor address capacity used ra owned t.dmem finished.frame
  apply restore_cps e base hc t s finished.saved
  intro flags
  apply (ret_cps e base hc (restoredState t s flags) ra _ ?_ ?_).2.2.2
  · simpa only [restoredState, UInt64.toBitVec_ofBitVec, finished.sp,
      BitVec.sub_add_cancel] using returnSlot
  · refine ⟨finished.observed, finished.written, ?_, finished.frame, finished.cursor, original⟩
    refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, finished.simd, returnSlot⟩
    simp only [restoredState, UInt64.toBitVec_ofBitVec, finished.sp, BitVec.sub_add_cancel]

end SszX86.NatMulWord

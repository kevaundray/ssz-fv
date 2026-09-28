import SszX86.BitVectorAddOwned
import SszX86.BitVectorFinishExactOwned
import SszX86.BitVectorWorldAdd

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- Exactly the machine state produced by the native rounding setup and CALL. -/
def finishAddCallee (u : MachineData) (quotient : NatOperand) (flags : StatusFlags)
    (ra : BitVec 64) : MachineData :=
  callState (roundSetupState u quotient.pointer quotient.payload flags) ra

theorem finish_add_positions (s u : MachineData) (saved : Saved) (length quotient : NatOperand)
    (data : Ssz.Bytes) (address capacity used : BitVec 64) (flags : StatusFlags) (ra : BitVec 64)
    (owned : Owned {s with dmem := u.dmem} saved length data address capacity used)
    (anchors : Anchors s u length) :
    (finishAddCallee u quotient flags ra).regs.rdi.toNat = s.regs.rsp.toNat + 16 ∧
    (finishAddCallee u quotient flags ra).regs.rsp.toNat = s.regs.rsp.toNat - 8 ∧
    (finishAddCallee u quotient flags ra).regs.r9 = s.regs.rbx := by
  have low : 72 ≤ s.regs.rsp.toBitVec.toNat := owned.stack_low
  have high : s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64 := owned.stack_bound
  refine ⟨?_, ?_, anchors.arena⟩
  · change (u.regs.rsp.toBitVec + 16#64).toNat = s.regs.rsp.toBitVec.toNat + 16
    rw [anchors.stack]
    bv_omega
  · change (u.regs.rsp.toBitVec - 8#64).toNat = s.regs.rsp.toBitVec.toNat - 8
    rw [anchors.stack]
    bv_omega

theorem finish_add_call_frame (s u : MachineData) (quotient : NatOperand)
    (flags : StatusFlags) (ra : BitVec 64) (stack : u.regs.rsp = s.regs.rsp)
    (low : 72 ≤ s.regs.rsp.toNat) (high : s.regs.rsp.toNat + 368 ≤ 2^64) :
    RegionsFrame u.dmem (finishAddCallee u quotient flags ra).dmem [(workStart s, workSize)] := by
  have location : (s.regs.rsp.toBitVec - 8#64).toNat = s.regs.rsp.toNat - 8 := by
    change (s.regs.rsp.toBitVec - 8#64).toNat = s.regs.rsp.toBitVec.toNat - 8
    have lowBV : 72 ≤ s.regs.rsp.toBitVec.toNat := low
    bv_omega
  have frame := work_store_regions s u.dmem (s.regs.rsp.toBitVec - 8#64) 8 ra.toInt
    (by rw [location]; unfold workStart; omega)
    (by rw [location]; unfold workStart workSize; omega)
    (by rw [location]; omega)
  simpa only [finishAddCallee, callState, NatDivision.callState, roundSetupState, stack,
    show (8 : BitVec 64) = 8#64 by decide] using frame

/-- Helper ownership is derived for every actual setup flag outcome. -/
theorem finish_add_owned (s u : MachineData) (saved : Saved) (length quotient : NatOperand)
    (data : Ssz.Bytes) (address capacity initialUsed currentUsed : BitVec 64)
    (writes : List (Nat × Nat)) (flags : StatusFlags) (ra : BitVec 64)
    (world : World s saved length data address capacity initialUsed currentUsed writes u.dmem)
    (anchors : Anchors s u length)
    (metadata : NatArithmetic.operandAt (widthLoad u.dmem) (s.regs.rsp.toNat + 208) quotient)
    (protectedOperand : OperandProtected s address capacity currentUsed quotient) :
    NatAdd.Owned (finishAddCallee u quotient flags ra) quotient (.small 1)
      address capacity currentUsed ra := by
  have calledWorld := world.call (u := roundSetupState u quotient.pointer quotient.payload flags)
    anchors.stack ra
  have callFrame := finish_add_call_frame s u quotient flags ra anchors.stack
    world.physical.stack_low world.physical.stack_bound
  have stored : quotient.At (widthLoad (finishAddCallee u quotient flags ra).dmem) := by
    apply callFrame.operand quotient metadata.2.2
    intro pointer words equal span member
    subst quotient
    simp only [List.mem_singleton] at member
    subst span
    exact protectedOperand.work
  apply add_owned s (finishAddCallee u quotient flags ra) saved length quotient data
    address capacity currentUsed ra calledWorld.physical
  · simp only [finishAddCallee, NatDivision.callState, roundSetupState,
      UInt64.toBitVec_ofBitVec, anchors.stack]
  · simp only [finishAddCallee, NatDivision.callState, roundSetupState,
      UInt64.toBitVec_ofBitVec, anchors.stack, show (8 : BitVec 64) = 8#64 by decide]
  · exact anchors.arena
  · rfl
  · rfl
  · rfl
  · rfl
  · exact stored
  · exact protectedOperand
  · exact NatDivision.call_slot_load _ _ ra

/-- The caller caches are physically outside the CALL store, before addition. -/
theorem finish_add_call_cache (s u : MachineData) (quotient : NatOperand)
    (flags : StatusFlags) (ra : BitVec 64) (stack : u.regs.rsp = s.regs.rsp)
    (low : 72 ≤ s.regs.rsp.toNat) (high : s.regs.rsp.toNat + 368 ≤ 2^64)
    (off : Nat) (inside : off + 8 ≤ 224) :
    Mem.loadInt (finishAddCallee u quotient flags ra).dmem
        (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) 8 =
      Mem.loadInt u.dmem (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) 8 := by
  have lowSetup : 8 ≤ (roundSetupState u quotient.pointer quotient.payload flags).regs.rsp.toBitVec.toNat := by
    simpa only [roundSetupState, stack, UInt64.toNat_toBitVec] using (show 8 ≤ s.regs.rsp.toNat by omega)
  have highSetup : (roundSetupState u quotient.pointer quotient.payload flags).regs.rsp.toBitVec.toNat + 224 ≤ 2^64 := by
    simpa only [roundSetupState, stack, UInt64.toNat_toBitVec] using
      (show s.regs.rsp.toNat + 224 ≤ 2^64 by omega)
  have kept := call_stack_read (roundSetupState u quotient.pointer quotient.payload flags) ra off 8
    lowSetup highSetup inside
  simpa only [finishAddCallee, roundSetupState, stack] using kept

end SszX86.BitVector

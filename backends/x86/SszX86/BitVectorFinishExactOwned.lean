import SszX86.BitVectorFinishExactMemory

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- The exact CALL is owned from the reached metadata and protected operand, not
from a hypothetical helper execution or an assumption about its comparison. -/
theorem finish_exact_owned (s u : MachineData) (saved : Saved) (length expected : NatOperand)
    (data : Ssz.Bytes) (address capacity used actual ra : BitVec 64)
    (owned : Owned {s with dmem := u.dmem} saved length data address capacity used)
    (stack : u.regs.rsp = s.regs.rsp) (actualRegister : u.regs.r14.toBitVec = actual)
    (metadata : NatArithmetic.operandAt (widthLoad u.dmem) (s.regs.rsp.toNat + 208) expected)
    (protectedOperand : OperandProtected s address capacity used expected) :
    NatExact.Owned (callState (exactSetupState u) ra) expected actual ra := by
  let c := callState (exactSetupState u) ra
  have low : 72 ≤ s.regs.rsp.toNat := owned.stack_low
  have high : s.regs.rsp.toNat + 368 ≤ 2^64 := owned.stack_bound
  have pushed : RegionsFrame u.dmem c.dmem [(s.regs.rsp.toNat - 8, 8)] := by
    have location : (s.regs.rsp.toBitVec - 8#64).toNat = s.regs.rsp.toNat - 8 := by
      change (s.regs.rsp.toBitVec - 8#64).toNat = s.regs.rsp.toBitVec.toNat - 8
      have bound : 72 ≤ s.regs.rsp.toBitVec.toNat := low
      bv_omega
    have frame := store_regions_frame u.dmem (s.regs.rsp.toBitVec - 8#64) 8 ra.toInt
      (by rw [location]; omega)
    simpa only [c, callState, NatDivision.callState, exactSetupState, stack,
      show (8 : BitVec 64) = 8#64 by decide, location] using frame
  have metadataRead (off : Nat) (inside : off + 8 ≤ 224) :
      widthLoad c.dmem (s.regs.rsp.toNat + off) 8 =
        widthLoad u.dmem (s.regs.rsp.toNat + off) 8 := by
    apply pushed.width _ _ (by omega)
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    unfold Body.Apart
    omega
  have operand : expected.At (widthLoad c.dmem) := by
    apply pushed.operand expected metadata.2.2
    intro pointer words equal span member
    subst expected
    have apart := protectedOperand.work
    simp only [List.mem_singleton] at member
    subst span
    simp only [Body.Apart, workStart, workSize] at apart ⊢
    omega
  have stored : NatArithmetic.operandAt (widthLoad c.dmem) (s.regs.rsp.toNat + 208) expected := by
    refine ⟨?_, ?_, operand⟩
    · rw [metadataRead 208 (by decide)]
      exact metadata.1
    · simpa only [Nat.add_assoc, Nat.reduceAdd, metadataRead 216 (by decide)] using metadata.2.1
  have protectedHere : OperandProtected {s with dmem := u.dmem} address capacity used expected := by
    cases expected with
    | small limb => trivial
    | large pointer words => exact protectedOperand.with_memory u.dmem
  apply exact_owned {s with dmem := u.dmem} c saved length expected data address capacity used
    actual ra owned
  · simp only [c, NatDivision.callState, exactSetupState, UInt64.toBitVec_ofBitVec, stack]
  · simp only [c, NatDivision.callState, exactSetupState, UInt64.toBitVec_ofBitVec, stack,
      show (8 : BitVec 64) = 8#64 by decide]
  · simp only [c, NatDivision.callState, exactSetupState, UInt64.toBitVec_ofBitVec, stack]
  · exact actualRegister
  · change Large.Mapped (Mem.storeInt u.dmem (u.regs.rsp.toBitVec - 8#64) 8 ra.toInt)
      (s.regs.rsp.toBitVec - 72#64) workSize
    exact Large.mapped_store _ _ _ _ _ _ owned.work_mapped
  · exact stored
  · exact protectedHere
  · exact NatDivision.call_slot_load _ _ ra

theorem finish_exact_slot (s u : MachineData) (saved : Saved) (length : NatOperand)
    (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (owned : Owned {s with dmem := u.dmem} saved length data address capacity used)
    (stack : u.regs.rsp = s.regs.rsp) : CallSlot u := by
  have read := Large.mapped_load u.dmem (s.regs.rsp.toBitVec - 72#64) workSize 64 8
    owned.work_mapped (by decide)
  simpa only [CallSlot, stack,
    show s.regs.rsp.toBitVec - 72#64 + BitVec.ofNat 64 64 = s.regs.rsp.toBitVec - 8#64
      by bv_omega] using read

end SszX86.BitVector

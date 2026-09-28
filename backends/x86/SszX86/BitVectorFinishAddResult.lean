import SszX86.BitVectorFinishAddSuccess
import SszX86.BitVectorFinishPost
import SszX86.BitVectorErrorsWorld

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- All actual add-result branches return the original public Post. Inputs are
reached physical memory and the executed helpers' resource trace, never a
future native branch, helper contract, or construction guard. -/
theorem finish_add_result_correct (e : Executable) (base : Int64) (hc : JointCodeAt e base)
    (s u : MachineData) (saved : Saved) (length quotient : NatOperand) (data : Ssz.Bytes)
    (remainder address capacity initialUsed currentUsed : BitVec 64)
    (original : Owned s saved length data address capacity initialUsed)
    (world : World s saved length data address capacity initialUsed currentUsed
      (SszNative.BitVector.run length data ⟨address.toNat, capacity.toNat, initialUsed.toNat⟩).writes u.dmem)
    (cursorValue : currentUsed.toNat =
      (SszNative.BitVector.run length data ⟨address.toNat, capacity.toNat, initialUsed.toNat⟩).used)
    (written : (SszNative.BitVector.run length data
      ⟨address.toNat, capacity.toNat, initialUsed.toNat⟩).writtenAt (widthLoad u.dmem))
    (protectedWrites : ∀ span ∈ (SszNative.BitVector.run length data
      ⟨address.toNat, capacity.toNat, initialUsed.toNat⟩).writes,
      Protected s address capacity currentUsed span.1 span.2)
    (anchors : Anchors s u length) (remainderReg : u.regs.r13.toBitVec = remainder)
    (divided : (SszNative.NatDivision.run length 8 address.toNat capacity.toNat initialUsed.toNat).result =
      .ok (quotient, remainder))
    (nonzero : remainder ≠ 0#64)
    (observed : NatArithmetic.AddResultAt (widthLoad u.dmem) (s.regs.rsp.toNat + 16)
      (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat
        (SszNative.NatDivision.run length 8 address.toNat capacity.toNat initialUsed.toNat).used).result)
    (protectedOperand : ∀ expected,
      (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat
        (SszNative.NatDivision.run length 8 address.toNat capacity.toNat initialUsed.toNat).used).result =
          .ok expected → OperandProtected s address capacity currentUsed expected) :
    Eventually (step e) (Post s saved length data address capacity initialUsed) (u, base + 1764) := by
  let outcome := SszNative.BitVector.run length data ⟨address.toNat, capacity.toNat, initialUsed.toNat⟩
  have nonzeroModel : remainder ≠ (0 : BitVec 64) := nonzero
  have privateObserved : NatArithmetic.AddResultAt (widthLoad u.dmem) (u.regs.rsp.toNat + 16)
      (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat
        (SszNative.NatDivision.run length 8 address.toNat capacity.toNat initialUsed.toNat).used).result := by
    simpa only [anchors.stack] using observed
  apply eventually_trans (step e) (Terminal s saved u.dmem data outcome.result) _ _
  · cases rounded : (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat
        (SszNative.NatDivision.run length 8 address.toNat capacity.toNat initialUsed.toNat).used).result with
    | error reason =>
      have resultEqual : outcome.result = .error (.arithmetic reason) := by
        simp only [outcome, SszNative.BitVector.run, divided, nonzeroModel, ↓reduceIte, rounded]
      rw [resultEqual]
      simp only [rounded, NatArithmetic.AddResultAt] at privateObserved
      let statusWord := (arithmeticErrorImage reason 0#32).reason
      have statusRead : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 80#64) 4 =
          some (statusWord.toNat : Int) := by
        apply errors_raw_read _ _ 80 4
        cases reason <;>
          simpa only [Nat.add_assoc, Nat.reduceAdd, statusWord, arithmeticErrorImage,
            show (32768#32).toNat = 32768 by decide,
            show (32770#32).toNat = 32770 by decide] using privateObserved.2.2.2.2.2.2.2.2
      have statusNonzero : statusWord ≠ 0#32 := by cases reason <;> decide
      apply add_status_cps e base hc.body u statusWord statusRead
      intro flags
      simp only [statusNonzero, ↓reduceIte]
      let v := addStatusState u statusWord flags
      have afterAnchors : Anchors s v length := by
        exact ⟨anchors.stack, anchors.arena, anchors.count, anchors.pointer, anchors.payload,
          anchors.outputCache, anchors.sourceCache⟩
      have privateMapped : Large.Mapped v.dmem (v.regs.rsp.toBitVec + 16#64) 72 := by
        have part := mapped_subrange u.dmem s.regs.rsp.toBitVec 224 16 72
          world.physical.body_mapped (by decide)
        simpa only [v, addStatusState, anchors.stack] using part
      have statusRegister : v.regs.rax.toBitVec.setWidth 32 = statusWord := by
        change (statusWord.setWidth 64).setWidth 32 = statusWord
        rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
      have statusLoaded : Mem.loadInt v.dmem (v.regs.rsp.toBitVec + 80#64) 4 =
          some ((v.regs.rax.toBitVec.setWidth 32).toNat : Int) := by
        rw [statusRegister]
        exact statusRead
      obtain ⟨padding, inputReads⟩ := add_reads_of_private v reason privateObserved privateMapped statusLoaded
      exact add_error_terminal e base hc.body s v saved data reason padding
        (error_suffix_at (u := v) world afterAnchors original.saved_at) inputReads
        (by simpa only [v, addStatusState, anchors.stack] using world.physical.body_mapped)
    | ok expected =>
      have resultEqual : outcome.result = SszNative.BitVector.finish length expected remainder data := by
        simp only [outcome, SszNative.BitVector.run, divided, nonzeroModel, ↓reduceIte, rounded]
      rw [resultEqual]
      simp only [rounded, NatArithmetic.AddResultAt] at privateObserved
      have statusRead : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 80#64) 4 =
          some ((0#32).toNat : Int) := by
        simp only [show (0#32).toNat = 0 by decide]
        errors_private_read 80 from privateObserved.2
      apply add_status_cps e base hc.body u 0#32 statusRead
      intro flags
      simp only [↓reduceIte]
      let v := addStatusState u 0#32 flags
      have afterAnchors : Anchors s v length := by
        exact ⟨anchors.stack, anchors.arena, anchors.count, anchors.pointer, anchors.payload,
          anchors.outputCache, anchors.sourceCache⟩
      exact finish_add_success_correct e base hc s v saved length expected data remainder
        address capacity initialUsed currentUsed _ world afterAnchors original.saved_at remainderReg
        (by simpa only [v, addStatusState, anchors.stack] using privateObserved.1)
        (protectedOperand expected rounded)
        (SszNative.BitVector.expected_of_round length quotient expected remainder
          address.toNat capacity.toNat initialUsed.toNat divided nonzero rounded)
  · intro t terminal
    exact Eventually.done _ (finish_post s saved length data address capacity initialUsed currentUsed
      u.dmem outcome rfl world cursorValue written protectedWrites t terminal)

end SszX86.BitVector

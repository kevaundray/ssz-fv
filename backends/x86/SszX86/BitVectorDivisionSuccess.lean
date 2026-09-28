import SszX86.BitVectorNoRound
import SszX86.BitVectorRounded
import SszX86.BitVectorFinishAddResult
import SszX86.BitVectorDivisionStage
import SszX86.BitVectorRoundStage

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

theorem rounded_correct (e : Executable) (base : Int64) (hc : JointCodeAt e base)
    (s u : MachineData) (saved : Saved) (length quotient : NatOperand) (data : Ssz.Bytes)
    (remainder address capacity used : BitVec 64)
    (owned : Owned s saved length data address capacity used)
    (divided : (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat).result =
      .ok (quotient, remainder)) (nonzero : remainder ≠ 0#64)
    (world : World s saved length data address capacity used
      (divisionCursor length address capacity used)
      (SszNative.BitVector.allocationWrites
        (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat)) u.dmem)
    (anchors : Anchors s u length) (remainderReg : u.regs.r13.toBitVec = remainder)
    (metadata : NatArithmetic.operandAt (widthLoad u.dmem) (s.regs.rsp.toNat + 208) quotient)
    (protectedOperand : OperandProtected s address capacity (divisionCursor length address capacity used) quotient)
    (written : SszNative.BitVector.allocationAt (widthLoad u.dmem)
      (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat)) :
    Eventually (step e) (Post s saved length data address capacity used) (u, base + 1727) := by
  apply eventually_trans (step e) _ _ _
    (rounded_reached e base hc s u saved length quotient data remainder address capacity used owned
      divided nonzero world anchors remainderReg metadata protectedOperand written)
  rintro ⟨v, pc⟩ reached
  have returnedPc : pc = base + 1764 := reached.pc
  subst pc
  exact finish_add_result_correct e base hc s v saved length quotient data remainder address capacity
    used _ owned reached.world reached.cursorValue reached.written reached.protectedWrites
    reached.anchors reached.remainderReg divided nonzero reached.observed reached.expectedProtected

/-- A successful divider is followed by the actual pair stores, optional real add,
exact check and terminal path; no later scope, padding or representation guard is
assumed. Every native helper and local store contributes to the final Post. -/
theorem division_success_post (e : Executable) (base : Int64) (hc : JointCodeAt e base)
    (s u : MachineData) (saved : Saved) (length quotient : NatOperand) (data : Ssz.Bytes)
    (remainder address capacity used : BitVec 64)
    (owned : Owned s saved length data address capacity used)
    (reached : DivisionReached base s saved length data address capacity used (u, base + 157))
    (divided : (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat).result =
      .ok (quotient, remainder)) :
    Eventually (step e) (Post s saved length data address capacity used) (u, base + 157) := by
  have positions := division_ready_positions s saved length data address capacity used
    (base + 157).toBitVec owned
  have observed := reached.post.observed
  rw [divided, positions.1] at observed
  have pointerRead : Mem.loadInt u.dmem (s.regs.rsp.toBitVec + 16#64) 8 =
      some (quotient.pointer.toNat : Int) :=
    errors_raw_read u.dmem s.regs.rsp 16 8 quotient.pointer.toNat observed.1.1
  have payloadRead : Mem.loadInt u.dmem (s.regs.rsp.toBitVec + 24#64) 8 =
      some (quotient.payload.toNat : Int) := by
    apply errors_raw_read u.dmem s.regs.rsp 24 8
    simpa only [Nat.add_assoc, Nat.reduceAdd] using observed.1.2.1
  have remainderRead : Mem.loadInt u.dmem (s.regs.rsp.toBitVec + 32#64) 8 =
      some (remainder.toNat : Int) := by
    apply errors_raw_read u.dmem s.regs.rsp 32 8
    simpa only [Nat.add_assoc, Nat.reduceAdd] using observed.2.1
  have statusRead : Mem.loadInt u.dmem (s.regs.rsp.toBitVec + 80#64) 4 = some ((0#32).toNat : Int) := by
    apply errors_raw_read u.dmem s.regs.rsp 80 4
    simpa only [Nat.add_assoc, Nat.reduceAdd, BitVec.toNat_zero] using observed.2.2
  have protectedOperand := division_quotient_owned s saved length quotient data address capacity used
    (base + 157).toBitVec remainder owned divided
  have protectedSpans := division_spans_protected s saved length data address capacity used
    (base + 157).toBitVec owned
  have highBV : s.regs.rsp.toBitVec.toNat + 224 ≤ 2^64 := by
    have high : s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64 := owned.stack_bound
    omega
  apply division_stage_cps e base hc.body s u saved length data address capacity used
    (divisionCursor length address capacity used) _ reached.world reached.anchors
    quotient.pointer quotient.payload remainder 0#32 statusRead pointerRead payloadRead remainderRead
  intro flags worldAfter anchorsAfter frameAfter
  simp only [↓reduceIte]
  let v := divisionResultState u quotient.pointer quotient.payload remainder 0#32 flags
  have quotientStored := work_frame_operand frameAfter quotient observed.1.2.2 protectedOperand
  have divisionWritten := work_frame_allocation frameAfter
    (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat)
    reached.post.written protectedSpans
  have pair := stack_pair_reads u.dmem s.regs.rsp.toBitVec 120 quotient.pointer quotient.payload
    highBV (by decide)
  have stack : u.regs.rsp = s.regs.rsp := reached.anchors.stack
  have stageMemory : v.dmem = stackPairMem u.dmem s.regs.rsp.toBitVec 120
      quotient.pointer quotient.payload := by
    dsimp only [v, divisionResultState]
    rw [stack]
    rfl
  have stagedPointer : Mem.loadInt v.dmem (s.regs.rsp.toBitVec + 120#64) 8 =
      some (quotient.pointer.toNat : Int) := by
    rw [stageMemory]
    exact pair.1
  have stagedPayload : Mem.loadInt v.dmem (s.regs.rsp.toBitVec + 128#64) 8 =
      some (quotient.payload.toNat : Int) := by
    rw [stageMemory]
    exact pair.2
  have remainderV : v.regs.r13.toBitVec = remainder := by
    simp only [v, divisionResultState, UInt64.toBitVec_ofBitVec]
  apply round_branch_owned_cps e base hc.body s v saved length quotient data address capacity used
    (divisionCursor length address capacity used) _ worldAfter anchorsAfter quotientStored protectedOperand
    stagedPointer stagedPayload
  intro roundFlags roundedWorld roundedAnchors metadata roundFrame
  let w := roundBranchState v quotient.pointer quotient.payload roundFlags
  have remainderW : w.regs.r13.toBitVec = remainder := remainderV
  have retained := work_frame_allocation roundFrame
    (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat)
    divisionWritten protectedSpans
  rw [remainderV]
  by_cases zero : remainder = 0#64
  · rw [ite_eq_left zero]
    exact no_round_correct e base hc s w saved length quotient data remainder address capacity used owned
      divided zero roundedWorld roundedAnchors remainderW metadata protectedOperand retained
  · rw [ite_eq_right zero]
    exact rounded_correct e base hc s w saved length quotient data remainder address capacity used owned
      divided zero roundedWorld roundedAnchors remainderW metadata protectedOperand retained

end SszX86.BitVector

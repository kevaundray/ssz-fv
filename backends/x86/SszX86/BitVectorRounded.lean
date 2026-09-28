import SszX86.BitVectorFinishAdd
import SszX86.BitVectorAllocationTrace
import SszX86.BitVectorQuotientOwned

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

structure RoundedResources (base : Int64) (s : MachineData) (saved : Saved)
    (length quotient : NatOperand) (data : Ssz.Bytes) (remainder address capacity used : BitVec 64)
    (t : MachineState) : Prop where
  pc : t.2 = base + 1764
  world : World s saved length data address capacity used
    (outcomeCursor (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat
      (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat).used))
    (SszNative.BitVector.run length data ⟨address.toNat, capacity.toNat, used.toNat⟩).writes t.1.dmem
  anchors : Anchors s t.1 length
  remainderReg : t.1.regs.r13.toBitVec = remainder
  observed : NatArithmetic.AddResultAt (widthLoad t.1.dmem) (s.regs.rsp.toNat + 16)
    (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat
      (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat).used).result
  cursorValue : (outcomeCursor (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat
      (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat).used)).toNat =
    (SszNative.BitVector.run length data ⟨address.toNat, capacity.toNat, used.toNat⟩).used
  written : (SszNative.BitVector.run length data
    ⟨address.toNat, capacity.toNat, used.toNat⟩).writtenAt (widthLoad t.1.dmem)
  protectedWrites : ∀ span ∈ (SszNative.BitVector.run length data
      ⟨address.toNat, capacity.toNat, used.toNat⟩).writes,
    Protected s address capacity
      (outcomeCursor (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat
        (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat).used)) span.1 span.2
  expectedProtected : ∀ expected,
    (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat
      (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat).used).result = .ok expected →
    OperandProtected s address capacity
      (outcomeCursor (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat
        (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat).used)) expected

/-- Both helpers have actually executed before any record of the second allocation
is added. The first helper's complete buffer survives even an add rejection. -/
theorem rounded_reached (e : Executable) (base : Int64) (hc : JointCodeAt e base)
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
    Eventually (step e) (RoundedResources base s saved length quotient data remainder address capacity used)
      (u, base + 1727) := by
  let d := SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat
  let r := SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat d.used
  let whole := SszNative.BitVector.run length data ⟨address.toNat, capacity.toNat, used.toNat⟩
  have cursorBefore := division_cursor_value s saved length data address capacity used (base + 157).toBitVec owned
  have nonzeroModel : remainder ≠ (0 : BitVec 64) := nonzero
  have projection : whole.divided = d ∧ whole.rounded = some r := by
    simp only [whole, SszNative.BitVector.run, divided, nonzeroModel, ↓reduceIte]
    cases (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat d.used).result <;>
      constructor <;> rfl
  have wholeWrites : whole.writes = SszNative.BitVector.allocationWrites d ++
      SszNative.BitVector.allocationWrites r := by
    simp only [SszNative.BitVector.Outcome.writes, projection.1, projection.2]
  have wholeUsed : whole.used = r.used := by
    simp only [SszNative.BitVector.Outcome.used, projection.2]
  have oldProtected := division_spans_protected s saved length data address capacity used
    (base + 157).toBitVec owned
  apply eventually_trans (step e) _ _ _
    (finish_add_reached e base hc s u saved length quotient data address capacity used
      (divisionCursor length address capacity used) _ world anchors metadata protectedOperand)
  intro t reached
  obtain ⟨flags, post, afterWorld, afterAnchors, remainderKept⟩ := reached
  let c := finishAddCallee u quotient flags (base + 1764).toBitVec
  have helper := finish_add_owned s u saved length quotient data address capacity used
    (divisionCursor length address capacity used) _ flags (base + 1764).toBitVec
    world anchors metadata protectedOperand
  have positions := finish_add_positions s u saved length quotient data address capacity
    (divisionCursor length address capacity used) flags (base + 1764).toBitVec world.physical anchors
  have calledWorld := world.call (u := roundSetupState u quotient.pointer quotient.payload flags)
    anchors.stack (base + 1764).toBitVec
  have low : 72 ≤ s.regs.rsp.toNat := world.physical.stack_low
  have high : s.regs.rsp.toNat + 368 ≤ 2^64 := world.physical.stack_bound
  have callFrame := call_work_frame s (roundSetupState u quotient.pointer quotient.payload flags)
    (base + 1764).toBitVec anchors.stack low high
  have calledWritten := work_frame_allocation callFrame d written oldProtected
  have retained := add_keeps_allocation s c quotient (.small 1) address capacity
    (divisionCursor length address capacity used) (base + 1764).toBitVec helper low
    positions.1 positions.2.1 positions.2.2 t post d oldProtected calledWritten
  have bounds := add_used_bounds c quotient (.small 1) address capacity
    (divisionCursor length address capacity used) (base + 1764).toBitVec helper
  have nextValue : (outcomeCursor (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat
      (divisionCursor length address capacity used).toNat)).toNat =
      (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat
        (divisionCursor length address capacity used).toNat).used := by
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt bounds.2 capacity.isLt)
  have newWritten : SszNative.BitVector.allocationAt (widthLoad t.1.dmem) r := by
    simpa only [SszNative.BitVector.allocationAt, r, d, cursorBefore] using post.written
  have newProtected := allocation_spans_protected s address capacity
    (outcomeCursor (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat
      (divisionCursor length address capacity used).toNat))
    (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat
      (divisionCursor length address capacity used).toNat)
    (calledWorld.add_written_protected helper)
  apply Eventually.done
  refine {
    pc := by simpa only [Int64.ofBitVec_toBitVec] using post.returned.pc
    world := ?_
    anchors := afterAnchors
    remainderReg := (congrArg UInt64.toBitVec remainderKept).trans remainderReg
    observed := ?_
    cursorValue := ?_
    written := ?_
    protectedWrites := ?_
    expectedProtected := ?_ }
  · change World s saved length data address capacity used (outcomeCursor r) whole.writes t.1.dmem
    rw [wholeWrites]
    simpa only [cursorBefore] using afterWorld
  · have observed := post.observed
    rw [positions.1, cursorBefore] at observed
    exact observed
  · change (outcomeCursor r).toNat = whole.used
    rw [wholeUsed]
    simpa only [cursorBefore] using nextValue
  · change whole.writtenAt (widthLoad t.1.dmem)
    constructor
    · simpa only [projection.1] using retained
    · intro rounded roundedAt
      rw [projection.2] at roundedAt
      cases Option.some.inj roundedAt
      exact newWritten
  · intro span member
    change span ∈ whole.writes at member
    rw [wholeWrites] at member
    rcases List.mem_append.mp member with earlier | later
    · have hp := (oldProtected span earlier).advance
        (next := outcomeCursor (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat
          (divisionCursor length address capacity used).toNat))
        (by rw [nextValue]; exact bounds.1) (by rw [nextValue]; exact bounds.2)
      simpa only [cursorBefore] using hp
    · simpa only [cursorBefore] using newProtected span (by simpa only [cursorBefore] using later)
  · intro expected success
    have nativeSuccess : (SszNative.NatAdd.run quotient (.small 1) address.toNat capacity.toNat
        (divisionCursor length address capacity used).toNat).result = .ok expected := by
      simpa only [cursorBefore] using success
    simpa only [cursorBefore] using calledWorld.round_result_protected helper nativeSuccess

end SszX86.BitVector

import SszX86.BitVectorErrorsDivisionMemory
import SszX86.BitVectorAllocationTrace
import SszX86.BitVectorFinishPost
import SszX86.BitVectorQuotientOwned

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- The actual PC157 rejection branch completes the original public postcondition.
The divider's cursor and every written allocation word are retained; no claim
that failure implies an empty allocation trace is required. -/
theorem division_error_post (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s u : MachineData) (saved : Saved) (length : NatOperand) (data : Ssz.Bytes)
    (address capacity used : BitVec 64)
    (owned : Owned s saved length data address capacity used)
    (reached : DivisionReached base s saved length data address capacity used (u, base + 157))
    (reason : NatArithmetic.Failure)
    (failed : (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat).result =
      .error reason) :
    Eventually (step e) (Post s saved length data address capacity used) (u, base + 157) := by
  let divided := SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat
  let outcome : SszNative.BitVector.Outcome := ⟨.error (.arithmetic reason), divided, none⟩
  have actual : outcome = SszNative.BitVector.run length data
      ⟨address.toNat, capacity.toNat, used.toNat⟩ := by
    simp only [outcome, divided, SszNative.BitVector.run, failed]
  have positions := division_ready_positions s saved length data address capacity used
    (base + 157).toBitVec owned
  have observed : NatArithmetic.errorAt (widthLoad u.dmem) (s.regs.rsp.toNat + 16) reason := by
    have result := reached.post.observed
    rw [failed, positions.1] at result
    exact result
  have nativeLoads := division_error_loads u.dmem s.regs.rsp reason observed
  have nonzero : (arithmeticErrorImage reason 0).reason ≠ 0#32 := by
    cases reason <;> decide
  have protectedWrites : ∀ span ∈ SszNative.BitVector.allocationWrites divided,
      Protected s address capacity (outcomeCursor divided) span.1 span.2 :=
    division_spans_protected s saved length data address capacity used (base + 157).toBitVec owned
  have cursorValue : (outcomeCursor divided).toNat = outcome.used := by
    simpa only [outcome, SszNative.BitVector.Outcome.used, outcomeCursor, divided, divisionCursor] using
      division_cursor_value s saved length data address capacity used (base + 157).toBitVec owned
  apply division_stage_cps e base hc s u saved length data address capacity used
    (outcomeCursor divided) (SszNative.BitVector.allocationWrites divided)
    reached.world reached.anchors 1#64 0#64 0#64 (arithmeticErrorImage reason 0).reason
    nativeLoads.1 nativeLoads.2.1 nativeLoads.2.2.1 nativeLoads.2.2.2
  intro flags stageWorld stageAnchors stageFrame
  rw [ite_eq_right nonzero]
  let v := divisionResultState u 1#64 0#64 0#64 (arithmeticErrorImage reason 0).reason flags
  change Eventually (step e) (Post s saved length data address capacity used) (v, base + 197)
  obtain ⟨padding, inputReads⟩ := division_error_staged_reads s u saved length data
    address capacity used (outcomeCursor divided) (SszNative.BitVector.allocationWrites divided)
    reached.anchors reason flags stageWorld stageAnchors observed
  have context := error_suffix_at stageWorld stageAnchors owned.saved_at
  have copied := division_error_terminal e base hc s v saved data reason padding context inputReads
  have writtenStage : SszNative.BitVector.allocationAt (widthLoad v.dmem) divided :=
    work_frame_allocation stageFrame divided reached.post.written protectedWrites
  have writtenBefore : outcome.writtenAt (widthLoad v.dmem) := by
    refine ⟨writtenStage, ?_⟩
    intro rounded impossible
    cases impossible
  have finalWorld : World s saved length data address capacity used (outcomeCursor divided)
      outcome.writes v.dmem := by
    simpa only [outcome, SszNative.BitVector.Outcome.writes, List.append_nil] using stageWorld
  have finalProtection : ∀ span ∈ outcome.writes,
      Protected s address capacity (outcomeCursor divided) span.1 span.2 := by
    simpa only [outcome, SszNative.BitVector.Outcome.writes, List.append_nil] using protectedWrites
  apply eventually_trans (step e) _ _ _ copied
  intro t terminal
  apply Eventually.done
  exact finish_post s saved length data address capacity used (outcomeCursor divided)
    v.dmem outcome actual finalWorld cursorValue writtenBefore finalProtection t terminal

end SszX86.BitVector

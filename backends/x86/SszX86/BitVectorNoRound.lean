import SszX86.BitVectorFinishExact
import SszX86.BitVectorFinishPost
import SszX86.BitVectorAllocationTrace
import SszX86.BitVectorQuotientOwned

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

theorem no_round_correct (e : Executable) (base : Int64) (hc : JointCodeAt e base)
    (s u : MachineData) (saved : Saved) (length quotient : NatOperand) (data : Ssz.Bytes)
    (remainder address capacity used : BitVec 64)
    (owned : Owned s saved length data address capacity used)
    (divided : (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat).result =
      .ok (quotient, remainder)) (zero : remainder = 0#64)
    (world : World s saved length data address capacity used
      (divisionCursor length address capacity used)
      (SszNative.BitVector.allocationWrites
        (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat)) u.dmem)
    (anchors : Anchors s u length) (remainderReg : u.regs.r13.toBitVec = remainder)
    (metadata : NatArithmetic.operandAt (widthLoad u.dmem) (s.regs.rsp.toNat + 208) quotient)
    (protectedOperand : OperandProtected s address capacity (divisionCursor length address capacity used) quotient)
    (written : SszNative.BitVector.allocationAt (widthLoad u.dmem)
      (SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat)) :
    Eventually (step e) (Post s saved length data address capacity used) (u, base + 4618) := by
  let outcome : SszNative.BitVector.Outcome :=
    ⟨SszNative.BitVector.finish length quotient remainder data,
      SszNative.NatDivision.run length 8 address.toNat capacity.toNat used.toNat, none⟩
  have zeroModel : remainder = (0 : BitVec 64) := zero
  have actual : outcome = SszNative.BitVector.run length data
      ⟨address.toNat, capacity.toNat, used.toNat⟩ := by
    simp only [SszNative.BitVector.run, divided, zeroModel, ↓reduceIte, outcome]
  have wholeWorld : World s saved length data address capacity used
      (divisionCursor length address capacity used) outcome.writes u.dmem := by
    simpa only [outcome, SszNative.BitVector.Outcome.writes, List.append_nil] using world
  have cursorValue : (divisionCursor length address capacity used).toNat = outcome.used :=
    division_cursor_value s saved length data address capacity used (base + 157).toBitVec owned
  have writtenBefore : outcome.writtenAt (widthLoad u.dmem) := by
    refine ⟨written, ?_⟩
    intro rounded impossible
    cases impossible
  have protectedWrites : ∀ span ∈ outcome.writes,
      Protected s address capacity (divisionCursor length address capacity used) span.1 span.2 := by
    simpa only [outcome, SszNative.BitVector.Outcome.writes, List.append_nil, outcomeCursor, divisionCursor] using
      division_spans_protected s saved length data address capacity used (base + 157).toBitVec owned
  have arithmetic := SszNative.BitVector.expected_of_division length quotient remainder
    address.toNat capacity.toNat used.toNat divided zero
  apply eventually_trans (step e) _ _ _
    (finish_exact_suffix_correct e base hc s u saved length quotient data remainder address capacity used
      (divisionCursor length address capacity used) _ world anchors owned.saved_at remainderReg
      metadata protectedOperand arithmetic)
  intro t terminal
  exact Eventually.done _ (finish_post s saved length data address capacity used
    (divisionCursor length address capacity used) u.dmem outcome actual wholeWorld cursorValue
    writtenBefore protectedWrites t terminal)

end SszX86.BitVector

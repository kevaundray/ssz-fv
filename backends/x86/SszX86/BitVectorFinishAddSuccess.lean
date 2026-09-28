import SszX86.BitVectorFinishExact
import SszX86.BitVectorRoundStage

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- The actual successful-add pair stores feed exact; their work writes are
included in the terminal frame, retaining every earlier allocation word. -/
theorem finish_add_success_correct (e : Executable) (base : Int64) (hc : JointCodeAt e base)
    (s u : MachineData) (saved : Saved) (length expected : NatOperand) (data : Ssz.Bytes)
    (remainder address capacity initialUsed currentUsed : BitVec 64) (writes : List (Nat × Nat))
    (world : World s saved length data address capacity initialUsed currentUsed writes u.dmem)
    (anchors : Anchors s u length)
    (original : SavedAt s.dmem s.regs.rsp.toBitVec saved)
    (remainderReg : u.regs.r13.toBitVec = remainder)
    (observed : NatArithmetic.operandAt (widthLoad u.dmem) (s.regs.rsp.toNat + 16) expected)
    (protectedOperand : OperandProtected s address capacity currentUsed expected)
    (arithmetic : SszNative.BitVector.Expected length expected remainder) :
    Eventually (step e)
      (Terminal s saved u.dmem data (SszNative.BitVector.finish length expected remainder data))
      (u, base + 4592) := by
  have low : 72 ≤ s.regs.rsp.toNat := world.physical.stack_low
  have high : s.regs.rsp.toNat + 368 ≤ 2^64 := world.physical.stack_bound
  have pointerRead : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 16#64) 8 =
      some (expected.pointer.toNat : Int) := by
    have read := widthLoad_eq u.dmem (s.regs.rsp.toNat + 16) 8 expected.pointer.toNat observed.1
    simpa only [anchors.stack, ← UInt64.toNat_toBitVec, width_address] using read
  have payloadRead : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 24#64) 8 =
      some (expected.payload.toNat : Int) := by
    have read := widthLoad_eq u.dmem (s.regs.rsp.toNat + 16 + 8) 8 expected.payload.toNat observed.2.1
    simpa only [Nat.add_assoc, Nat.reduceAdd, anchors.stack, ← UInt64.toNat_toBitVec, width_address]
      using read
  apply round_success_cps e base hc.body u expected.pointer expected.payload
    (by simpa only [anchors.stack] using world.physical.body_mapped) pointerRead payloadRead
  have afterWorld := round_stage_world world anchors expected.pointer expected.payload u.status
  have afterAnchors := round_stage_anchors anchors high expected.pointer expected.payload u.status
  have metadata := round_stage_operand anchors low high observed.2.2 protectedOperand u.status
  have workFrame := round_stage_frame anchors low high expected.pointer expected.payload u.status
  have frame : RegionsFrame u.dmem
      (roundBranchState u expected.pointer expected.payload u.status).dmem (finishRegions s) := by
    apply workFrame.weaken
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    simp [finishRegions]
  have execution := finish_exact_suffix_correct e base hc s
    (roundBranchState u expected.pointer expected.payload u.status) saved length expected data
    remainder address capacity initialUsed currentUsed writes afterWorld afterAnchors original
    remainderReg metadata protectedOperand arithmetic
  apply eventually_trans (step e) _ _ _ execution
  intro t terminal
  exact Eventually.done _ ⟨terminal.observed, terminal.returned,
    finish_frame_trans frame terminal.frame⟩

end SszX86.BitVector

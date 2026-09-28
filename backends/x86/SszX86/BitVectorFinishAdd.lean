import SszX86.BitVectorFinishAddOwned

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

def FinishAddReached (base : Int64) (s u : MachineData) (saved : Saved)
    (length quotient : NatOperand) (data : Ssz.Bytes)
    (address capacity initialUsed currentUsed : BitVec 64) (writes : List (Nat × Nat))
    (t : MachineState) : Prop :=
  ∃ flags, NatAdd.Post (finishAddCallee u quotient flags (base + 1764).toBitVec)
      quotient (.small 1) address capacity currentUsed (base + 1764).toBitVec t ∧
    World s saved length data address capacity initialUsed
      (outcomeCursor (SszNative.NatAdd.run quotient (.small 1)
        address.toNat capacity.toNat currentUsed.toNat))
      (writes ++ SszNative.BitVector.allocationWrites (SszNative.NatAdd.run quotient (.small 1)
        address.toNat capacity.toNat currentUsed.toNat)) t.1.dmem ∧
    Anchors s t.1 length ∧ t.1.regs.r13 = u.regs.r13

/-- The real optional-add setup and CALL return at 1764 on every allocator outcome.
Mapping comes from the actual helper execution, not a strengthened assumed Post. -/
theorem finish_add_reached (e : Executable) (base : Int64) (hc : JointCodeAt e base)
    (s u : MachineData) (saved : Saved) (length quotient : NatOperand) (data : Ssz.Bytes)
    (address capacity initialUsed currentUsed : BitVec 64) (writes : List (Nat × Nat))
    (world : World s saved length data address capacity initialUsed currentUsed writes u.dmem)
    (anchors : Anchors s u length)
    (metadata : NatArithmetic.operandAt (widthLoad u.dmem) (s.regs.rsp.toNat + 208) quotient)
    (protectedOperand : OperandProtected s address capacity currentUsed quotient) :
    Eventually (step e)
      (FinishAddReached base s u saved length quotient data address capacity initialUsed currentUsed writes)
      (u, base + 1727) := by
  have pointerRead : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 208#64) 8 =
      some (quotient.pointer.toNat : Int) := by
    have read := widthLoad_eq u.dmem (s.regs.rsp.toNat + 208) 8 quotient.pointer.toNat metadata.1
    simpa only [anchors.stack, ← UInt64.toNat_toBitVec, width_address] using read
  have payloadRead : Mem.loadInt u.dmem (u.regs.rsp.toBitVec + 216#64) 8 =
      some (quotient.payload.toNat : Int) := by
    have read := widthLoad_eq u.dmem (s.regs.rsp.toNat + 208 + 8) 8 quotient.payload.toNat metadata.2.1
    simpa only [Nat.add_assoc, Nat.reduceAdd, anchors.stack, ← UInt64.toNat_toBitVec, width_address]
      using read
  apply round_setup_cps e base hc.body u quotient.pointer quotient.payload pointerRead payloadRead
  intro flags
  let c := finishAddCallee u quotient flags (base + 1764).toBitVec
  have helper := finish_add_owned s u saved length quotient data address capacity initialUsed currentUsed
    writes flags (base + 1764).toBitVec world anchors metadata protectedOperand
  have positions := finish_add_positions s u saved length quotient data address capacity currentUsed
    flags (base + 1764).toBitVec world.physical anchors
  have calledWorld := world.call (u := roundSetupState u quotient.pointer quotient.payload flags)
    anchors.stack (base + 1764).toBitVec
  have slot := finish_exact_slot s (roundSetupState u quotient.pointer quotient.payload flags)
    saved length data address capacity currentUsed world.physical anchors.stack
  apply add_call_cps e base hc.body (roundSetupState u quotient.pointer quotient.payload flags) _ slot
  have execution := NatAdd.add_correct e (base + Int64.ofInt addOffset) hc.add c quotient (.small 1)
    address capacity currentUsed (base + 1764).toBitVec helper
  have mappedExecution := Mapping.retains_mapping e _ _ execution
  apply eventually_trans (step e) _ _ _ mappedExecution
  intro t reached
  obtain ⟨post, mapping⟩ := reached
  have worldAfter := calledWorld.add helper positions.1 positions.2.1 positions.2.2 post mapping
  have low : 72 ≤ s.regs.rsp.toNat := world.physical.stack_low
  have high : s.regs.rsp.toNat + 368 ≤ 2^64 := world.physical.stack_bound
  have outputProtected := add_stack_protected s c saved length data address capacity currentUsed
    calledWorld.physical positions.1 positions.2.1
    (congrArg UInt64.toBitVec positions.2.2) 8 8 (by decide) (Or.inl (by decide))
  have sourceProtected := add_stack_protected s c saved length data address capacity currentUsed
    calledWorld.physical positions.1 positions.2.1
    (congrArg UInt64.toBitVec positions.2.2) 104 8 (by decide) (Or.inr (by decide))
  have outputKept := add_stack_load s c quotient (.small 1) address capacity currentUsed
    (base + 1764).toBitVec helper t.1.dmem post.frame 8 8 outputProtected
  have sourceKept := add_stack_load s c quotient (.small 1) address capacity currentUsed
    (base + 1764).toBitVec helper t.1.dmem post.frame 104 8 sourceProtected
  have outputBefore := finish_add_call_cache s u quotient flags (base + 1764).toBitVec
    anchors.stack low high 8 (by decide)
  have sourceBefore := finish_add_call_cache s u quotient flags (base + 1764).toBitVec
    anchors.stack low high 104 (by decide)
  have stack : t.1.regs.rsp = s.regs.rsp := by
    apply UInt64.toBitVec_inj.mp
    have equal := post.returned.sp
    simp only [c, finishAddCallee, callState, NatDivision.callState, roundSetupState,
      UInt64.toBitVec_ofBitVec, anchors.stack] at equal
    bv_omega
  have afterAnchors : Anchors s t.1 length := by
    refine ⟨stack, post.returned.rbx.trans anchors.arena, post.returned.r14.trans anchors.count,
      ?_, ?_, outputKept.trans (outputBefore.trans anchors.outputCache),
      sourceKept.trans (sourceBefore.trans anchors.sourceCache)⟩
    · rw [post.returned.r15]
      exact anchors.pointer
    · rw [post.returned.r12]
      exact anchors.payload
  exact Eventually.done _ ⟨flags, post, worldAfter, afterAnchors, post.returned.r13⟩

end SszX86.BitVector

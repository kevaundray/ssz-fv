import SszX86.HashCombineLive
import SszX86.HashCombineCopyMemory
import SszX86.HashFinalizeProofs
import SszX86.BitVectorMappingClosure

namespace SszX86.Hash.Combine
open SszNative.HashStream

def combinedState (left right : ByteArray) : Model :=
  (update (update new left).state right).state

/-- The in-place state is passed to the proved finalizer at its real linked
entry; mapping retention is derived from execution, not added to its contract. -/
theorem finish_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (compress : CompressionCorrect e root) (entry : MachineData) (left right : ByteArray)
    (ra : BitVec 64) (pre : CombinePre root entry left right ra) (s : MachineData)
    (live : Live root entry left right ra s.dmem)
    (stored : StateAt s.dmem (s.regs.rsp.toBitVec + 8) (combinedState left right))
    (sp : s.regs.rsp.toBitVec = entry.regs.rsp.toBitVec - 168)
    (out : s.regs.rbx = entry.regs.rdi) :
    Eventually (step e) (CombinePost entry left right ra) (s, root + 399) := by
  let args := finalizeArgs s
  let callee := callState args (root + 412).toBitVec
  have calleeSP : callee.regs.rsp.toBitVec = entry.regs.rsp.toBitVec - 176 := by
    simp only [callee, args, callState, Emit.callState, finalizeArgs,
      UInt64.toBitVec_ofBitVec, sp]
    bv_omega
  have calleeState : callee.regs.rsi.toBitVec = entry.regs.rsp.toBitVec - 160 := by
    simp only [callee, args, callState, Emit.callState, finalizeArgs,
      UInt64.toBitVec_ofBitVec, sp]
    bv_omega
  have calleeOut : callee.regs.rdi.toBitVec = entry.regs.rdi.toBitVec := by
    simp only [callee, args, callState, Emit.callState, finalizeArgs, out]
  have stateAddress : s.regs.rsp.toBitVec + 8 = entry.regs.rsp.toBitVec - 160 := by
    rw [sp]
    bv_omega
  have stackAddress : (entry.regs.rsp.toBitVec - 176) - 192 =
      entry.regs.rsp.toBitVec - 368 := by bv_omega
  have callFrame : MemoryFrame s.dmem callee.dmem
      (DrainWritable (entry.regs.rsp.toBitVec - 168)) := by
    apply frame_mono _ _ _ _ (storeInt_frame _ _ _ _)
    intro a inside
    rcases inside with ⟨i, hi, equal⟩
    right
    refine ⟨160 + i, by omega, ?_⟩
    rw [equal]
    simp only [args, finalizeArgs, sp]
    bv_omega
  have callMapping : MappedPreserved s.dmem callee.dmem := by
    intro p n hm
    exact Large.mapped_store _ _ _ _ _ _ hm
  have liveCall := Live.after root entry left right ra pre _ _ live callFrame callMapping
  have calleePre : FinalizePre root callee (combinedState left right) (root + 412).toBitVec := by
    refine ⟨?_, ?_, ?_, ?_, ?_, by simpa only [calleeOut] using pre.outputPhysical,
      ?_, ?_, ?_, liveCall.tables, pre.tablePhysical, ?_,
      by simpa only [calleeOut] using pre.tablesOutput, ?_⟩
    · have h := call_state_preserved args (root + 412).toBitVec (combinedState left right) stored
      simpa only [callee, args, callState, Emit.callState, finalizeArgs,
        UInt64.toBitVec_ofBitVec] using h
    · rw [calleeOut]
      exact liveCall.output
    · rw [calleeSP]
      exact stack_subrange _ _ 368 176 192 liveCall.stack (by decide)
    · refine ⟨?_, Emit.call_return_slot args (root + 412).toBitVec⟩
      rw [calleeSP]
      unfold Physical
      have low := pre.stack.1
      have high := entry.regs.rsp.toBitVec.isLt
      bv_omega
    · rw [calleeState]
      unfold Physical
      have low := pre.stack.1
      have high := entry.regs.rsp.toBitVec.isLt
      bv_omega
    · rw [calleeState, calleeOut]
      intro i hi j hj equal
      apply pre.stackOutput (208 + i) (by omega) j hj
      rw [← equal]
      bv_omega
    · rw [calleeSP, calleeState, stackAddress]
      intro i hi j hj equal
      bv_omega
    · rw [calleeSP, calleeOut, stackAddress]
      intro i hi j hj
      exact pre.stackOutput i (by omega) j hj
    · rw [calleeState]
      constructor
      · intro i hi j hj equal
        apply pre.tablesStack.1 i hi (208 + j) (by omega)
        rw [equal]
        bv_omega
      · intro i hi j hj equal
        apply pre.tablesStack.2 i hi (208 + j) (by omega)
        rw [equal]
        bv_omega
    · rw [calleeSP, stackAddress]
      exact pre.tablesStack
  apply finalize_args_runs e root hc.combine s
  apply combine_call407_cps e root hc.combine args
  · have sub := mapped_subrange _ _ 368 192 8 live.stack.2 (by decide)
    have address : (entry.regs.rsp.toBitVec - 368) + BitVec.ofNat 64 192 =
        s.regs.rsp.toBitVec - 8 := by rw [sp]; bv_omega
    simpa only [address] using sub
  · have run := finalize_correct e root hc compress callee (combinedState left right)
      (root + 412).toBitVec calleePre
    apply eventually_trans (step e) _ _ _ (BitVector.Mapping.retains_mapping e _ _ run)
    rintro ⟨t, pc⟩ ⟨post, mapping⟩
    have returnedPc : pc = root + 412 := by
      simpa only [Int64.ofBitVec_toBitVec] using post.returned.1
    subst pc
    have returnedSp : t.regs.rsp.toBitVec = entry.regs.rsp.toBitVec - 168 := by
      have h := post.returned.2.1
      rw [calleeSP] at h
      rw [h]
      bv_omega
    have helperSubset : ∀ a, FinalizeWritable callee a → CombineWritable entry a := by
      intro a inside
      rcases inside with h | ⟨i, hi, equal⟩ | ⟨i, hi, equal⟩
      · exact Or.inl (by simpa only [calleeOut] using h)
      · right
        refine ⟨208 + i, by omega, ?_⟩
        rw [equal, calleeState]
        bv_omega
      · right
        exact ⟨i, hi, by simpa only [calleeSP, stackAddress] using equal⟩
    have wholeFrame : MemoryFrame entry.dmem t.dmem (CombineWritable entry) := by
      intro a outside
      exact (post.frame a (fun h => outside (helperSubset a h))).trans (liveCall.frame a outside)
    have loadPreserved (offset : Nat) (low : 120 ≤ offset) (high : offset ≤ 168) :
        Mem.loadInt t.dmem ((entry.regs.rsp.toBitVec - 168) + BitVec.ofNat 64 offset) 8 =
          Mem.loadInt callee.dmem ((entry.regs.rsp.toBitVec - 168) + BitVec.ofNat 64 offset) 8 := by
      apply Emit.frame_load callee.dmem t.dmem (FinalizeWritable callee) post.frame
      intro i hi inside
      rcases inside with ⟨j, hj, equal⟩ | ⟨j, hj, equal⟩ | ⟨j, hj, equal⟩
      · rw [calleeOut] at equal
        apply pre.stackOutput (200 + offset + i) (by omega) j hj
        rw [← equal]
        bv_omega
      · rw [calleeState] at equal
        bv_omega
      · rw [calleeSP, stackAddress] at equal
        bv_omega
    have savedAfter : SavedAt t.dmem t.regs.rsp.toBitVec entry := by
      rw [returnedSp]
      exact ⟨(loadPreserved 120 (by decide) (by decide)).trans liveCall.saves.rbx,
        (loadPreserved 128 (by decide) (by decide)).trans liveCall.saves.r12,
        (loadPreserved 136 (by decide) (by decide)).trans liveCall.saves.r13,
        (loadPreserved 144 (by decide) (by decide)).trans liveCall.saves.r14,
        (loadPreserved 152 (by decide) (by decide)).trans liveCall.saves.r15,
        (loadPreserved 160 (by decide) (by decide)).trans liveCall.saves.rbp⟩
    have returnAfter : Mem.loadInt t.dmem (t.regs.rsp.toBitVec + 168) 8 =
        some (Int.ofBytes (wordBytes ra)) := by
      rw [returnedSp, loadPreserved 168 (by decide) (by decide)]
      have address : entry.regs.rsp.toBitVec - 168 + 168 = entry.regs.rsp.toBitVec := by bv_omega
      simpa only [address] using liveCall.returnSlot
    apply epilogue_runs e root hc.combine t entry ra savedAfter returnAfter
    intro flags
    apply Eventually.done
    refine ⟨returnedState_abi t entry flags ra returnedSp, ?_, ?_, ?_, wholeFrame, ?_⟩
    · simpa only [returnedState, calleeOut, combinedState, combine] using post.digest
    · apply bytesAt_frame entry.dmem t.dmem _ _ _ pre.left wholeFrame
      intro i hi inside
      have hi' : i < left.size := by simpa only [Array.length_toList, ByteArray.size_data] using hi
      rcases inside with ⟨j, hj, equal⟩ | ⟨j, hj, equal⟩
      · exact pre.leftOutput i hi' j hj equal
      · exact pre.leftStack i hi' j hj equal
    · apply bytesAt_frame entry.dmem t.dmem _ _ _ pre.right wholeFrame
      intro i hi inside
      have hi' : i < right.size := by simpa only [Array.length_toList, ByteArray.size_data] using hi
      rcases inside with ⟨j, hj, equal⟩ | ⟨j, hj, equal⟩
      · exact pre.rightOutput i hi' j hj equal
      · exact pre.rightStack i hi' j hj equal
    · exact ⟨liveCall.stack.1, mapping _ _ liveCall.stack.2⟩

end SszX86.Hash.Combine

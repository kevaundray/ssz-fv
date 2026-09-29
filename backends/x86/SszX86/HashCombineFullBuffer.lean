import SszX86.HashCombineStores
import SszX86.HashCombineBodyMemory

namespace SszX86.Hash.Combine
open SszNative.HashStream

structure FullBufferPost (root : Int64) (s : MachineData) (state : Model)
    (source : BitVec 64) (input : ByteArray) (t : MachineState) : Prop where
  pc : t.2 = root + 331
  state : StateAt t.1.dmem (s.regs.rsp.toBitVec + 8)
    {state with chaining := compressBuffer state.chaining state.buffer, buffered := ⟨0, by decide⟩}
  memory : DrainMemory root t.1.dmem s.regs.rsp.toBitVec source input
  frame : MemoryFrame s.dmem t.1.dmem (DrainWritable s.regs.rsp.toBitVec)
  mapping : MappedPreserved s.dmem t.1.dmem
  rsp : t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec
  rbx : t.1.regs.rbx = s.regs.rbx
  r12 : t.1.regs.r12 = s.regs.r12
  right : t.1.regs.r15.toBitVec = s.regs.r15.toBitVec + s.regs.rbp.toBitVec
  remaining : t.1.regs.r14.toNat = s.regs.r14.toNat - s.regs.rbp.toNat

/-- At PC303 the counter may be the raw value64. The pre-store StateAt and its
counter-only frame suffice to justify compression and reconstruct after reset. -/
theorem full_buffer_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (compress : CompressionCorrect e root) (s : MachineData) (before : DataMem)
    (state : Model) (source : BitVec 64) (input : ByteArray)
    (memory : DrainMemory root s.dmem s.regs.rsp.toBitVec source input)
    (stored : StateAt before (s.regs.rsp.toBitVec + 8) state)
    (counterFrame : MemoryFrame before s.dmem
      (fun a => InSpan a (s.regs.rsp.toBitVec + 104) 8))
    (chainReg : s.regs.r12.toBitVec = s.regs.rsp.toBitVec + 72)
    (countBound : s.regs.rbp.toNat ≤ s.regs.r14.toNat) :
    Eventually (step e) (FullBufferPost root s state source input) (s, root + 303) := by
  have chainAddress : (s.regs.rsp.toBitVec + 8) + 64 = s.regs.rsp.toBitVec + 72 := by
    bv_omega
  have chain : ChainingAt s.dmem (s.regs.rsp.toBitVec + 72) state.chaining := by
    apply bytesAt_frame _ _ _ _ _
      (by simpa only [chainAddress] using stateAt_chaining _ _ _ stored) counterFrame
    intro i hi inside
    have hi' : i < 32 := by simpa only [chainingBytes_length] using hi
    rcases inside with ⟨j, hj, equal⟩
    bv_omega
  have buffer : BytesAt s.dmem (s.regs.rsp.toBitVec + 8) state.buffer.toList := by
    apply bytesAt_frame _ _ _ _ _ (stateAt_buffer _ _ _ stored) counterFrame
    intro i hi inside
    have hi' : i < 64 := by simpa only [Vector.length_toList] using hi
    rcases inside with ⟨j, hj, equal⟩
    bv_omega
  apply buffer_advance_runs e root hc.combine s
  intro flags
  let args := bufferCompressionArgs (bufferAdvanced s flags)
  have pre := buffer_compression_pre root args state.chaining state.buffer chainReg rfl
    chain buffer memory.statePhysical memory.stack memory.stackState memory.tables
    memory.tablePhysical memory.tablesState memory.tablesStack
  apply buffer_compression_args_runs e root hc.combine
  apply combine_call317_cps e root hc.combine args
  · have sub := mapped_subrange _ _ 168 160 8 memory.stack.2 (by decide)
    have same : s.regs.rsp.toBitVec - 168 + BitVec.ofNat 64 160 = s.regs.rsp.toBitVec - 8 := by
      bv_omega
    simpa only [same] using sub
  · apply eventually_trans (step e) _ _ _
      (compression_helper_runs e root hc.compress compress args (root + 322).toBitVec
        state.chaining state.buffer pre)
    rintro ⟨t, pc⟩ post
    have pc' : pc = root + 322 := by
      simpa only [Int64.ofBitVec_toBitVec] using post.returned.1
    subst pc
    have sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec := compression_stack args _ _ _ _ post
    have saved := compression_saved args _ _ _ _ post
    have helperFrame : MemoryFrame s.dmem t.dmem (DrainWritable s.regs.rsp.toBitVec) :=
      compression_frame_drain args _ _ _ _ chainReg post
    have resetFrame : MemoryFrame t.dmem (storeWord t 104 0).dmem
        (DrainWritable s.regs.rsp.toBitVec) := by
      simpa only [sp] using storeWord_frame t 104 0 (by decide) (by decide)
    have frame : MemoryFrame s.dmem (storeWord t 104 0).dmem
        (DrainWritable s.regs.rsp.toBitVec) := by
      intro a outside
      exact (resetFrame a outside).trans (helperFrame a outside)
    have mapping : MappedPreserved s.dmem (storeWord t 104 0).dmem := by
      intro p n hm
      exact storeWord_mapping t 104 0 p n (post.mapped p n hm)
    have chained : ChainingAt (storeWord t 104 0).dmem
        ((s.regs.rsp.toBitVec + 8) + 64) (compressBuffer state.chaining state.buffer) := by
      apply bytesAt_frame _ _ _ _ _
        (by simpa only [args, bufferCompressionArgs, bufferAdvanced,
          UInt64.toBitVec_ofBitVec, chainReg, chainAddress] using post.state)
        (storeInt_frame _ _ _ _)
      intro i hi inside
      have hi' : i < 32 := by simpa only [chainingBytes_length] using hi
      rcases inside with ⟨j, hj, equal⟩
      simp only [sp, chainAddress] at equal
      bv_omega
    have stateFinal : StateAt (storeWord t 104 0).dmem (s.regs.rsp.toBitVec + 8)
        {state with chaining := compressBuffer state.chaining state.buffer,
          buffered := ⟨0, by decide⟩} := by
      apply stateAt_replace_chaining_buffered before _ _ state _ ⟨0, by decide⟩
        (fun a => InSpan a (s.regs.rsp.toBitVec - 168) 168)
        memory.statePhysical stored chained
      · intro i hi
        have location : (s.regs.rsp.toBitVec + 8) + BitVec.ofNat 64 (96 + i) =
            (s.regs.rsp.toBitVec + 104) + BitVec.ofNat 64 i := by bv_omega
        simpa only [storeWord, sp, location] using
          word_store_bytes t.dmem (s.regs.rsp.toBitVec + 104) 0 i hi
      · intro a outside
        have noCounter : ¬ InSpan a (s.regs.rsp.toBitVec + 104) 8 := by
          rintro ⟨i, hi, equal⟩
          apply outside
          left
          refine ⟨32 + i, by omega, ?_⟩
          rw [equal]
          bv_omega
        have noChain : ¬ InSpan a (s.regs.rsp.toBitVec + 72) 32 := by
          rintro ⟨i, hi, equal⟩
          exact outside (Or.inl ⟨i, by omega, by simpa only [chainAddress] using equal⟩)
        have noStack : ¬ InSpan a (s.regs.rsp.toBitVec - 168) 168 :=
          fun h => outside (Or.inr h)
        rw [storeInt_frame t.dmem (t.regs.rsp.toBitVec + 104) 8 0 a
          (by simpa only [sp] using noCounter)]
        rw [post.frame a (by
          rintro (h | h)
          · exact noChain (by simpa only [args, bufferCompressionArgs, bufferAdvanced, chainReg] using h)
          · exact noStack h)]
        exact counterFrame a noCounter
      · intro i hi inside
        rcases inside with ⟨j, hj, equal⟩
        exact memory.stackState j hj i hi equal.symm
    apply buffer_reset_runs e root hc.combine t
    · have h := post.mapped _ _ memory.state
      have part := mapped_subrange _ _ 112 96 8 h (by decide)
      have location : (s.regs.rsp.toBitVec + 8) + BitVec.ofNat 64 96 =
          s.regs.rsp.toBitVec + 104 := by bv_omega
      simpa only [sp, location] using part
    · apply Eventually.done
      refine ⟨rfl, stateFinal,
        DrainMemory.after root s.dmem _ _ _ _ memory frame mapping,
        frame, mapping, sp, saved.1, saved.2.2.1, ?_, ?_⟩
      · have h := congrArg UInt64.toBitVec saved.2.2.2.2.2
        simpa only [args, bufferCompressionArgs, bufferAdvanced, UInt64.toBitVec_ofBitVec,
          storeWord] using h
      · have h := congrArg UInt64.toNat saved.2.2.2.2.1
        simp only [args, bufferCompressionArgs, bufferAdvanced] at h
        change t.regs.r14.toNat = (s.regs.r14.toBitVec - s.regs.rbp.toBitVec).toNat at h
        rw [h]
        simp only [BitVec.toNat_sub]
        have high := s.regs.r14.toBitVec.isLt
        have low := s.regs.rbp.toBitVec.isLt
        omega

end SszX86.Hash.Combine

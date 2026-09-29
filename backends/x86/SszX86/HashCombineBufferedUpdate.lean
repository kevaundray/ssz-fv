import SszX86.HashCombineUpdate

namespace SszX86.Hash.Combine
open SszNative.HashStream

/-- The native buffered-right path: bounded copy, transient occupancy, optional
buffer compression, then the direct loop over the untouched right allocation. -/
theorem buffered_right_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (compress : CompressionCorrect e root) (s : MachineData) (state : Model)
    (source : BitVec 64) (input : ByteArray)
    (memory : DrainMemory root s.dmem s.regs.rsp.toBitVec source input)
    (stored : StateAt s.dmem (s.regs.rsp.toBitVec + 8)
      {state with byteLen := state.byteLen + UInt64.ofNat input.size})
    (nonempty : state.buffered.val ≠ 0)
    (chainReg : s.regs.r12.toBitVec = s.regs.rsp.toBitVec + 72)
    (sourceReg : s.regs.r15.toBitVec = source)
    (countReg : s.regs.r14.toNat = input.size)
    (bufferedReg : s.regs.r13.toNat = state.buffered.val) :
    Eventually (step e) (UpdatePost root s state input) (s, root + 249) := by
  let count := min (64 - state.buffered.val) input.size
  have countSource : count ≤ input.size := Nat.min_le_right _ _
  have countBuffer : state.buffered.val + count ≤ 64 := by
    have := state.buffered.isLt
    have := Nat.min_le_left (64 - state.buffered.val) input.size
    omega
  have occupancy : s.regs.r13.toBitVec = BitVec.ofNat 64 state.buffered.val := by
    rw [← bufferedReg]
    simpa only [BitVec.setWidth_eq] using (BitVec.ofNat_toNat s.regs.r13.toBitVec).symm
  let counted : Model := {state with byteLen := state.byteLen + UInt64.ofNat input.size}
  apply select_count_runs e root hc.combine s (by rw [bufferedReg]; exact state.buffered.isLt)
  intro selectedFlags
  apply buffer_copy_args_runs e root hc.combine (selectedCount s selectedFlags)
  intro addressFlags
  let args := bufferCopyArgs (selectedCount s selectedFlags) addressFlags
  have destination : args.regs.rdi.toBitVec =
      (s.regs.rsp.toBitVec + 8) + BitVec.ofNat 64 state.buffered.val := by
    simp only [args, bufferCopyArgs, selectedCount, UInt64.toBitVec_ofBitVec, occupancy]
    bv_omega
  have copyCount : args.regs.rdx.toBitVec = BitVec.ofNat 64 count := by
    simp only [args, bufferCopyArgs, selectedCount, UInt64.toBitVec_ofNat,
      bufferedReg, countReg, count]
  have copyRun := copy_slice_runs e root hc .bufferedRight args source input 0
    state.buffered.val count memory (by omega) countBuffer
    (by simpa only [args, bufferCopyArgs, selectedCount, BitVec.add_zero] using sourceReg)
    destination copyCount
  apply eventually_trans (step e) _ _ _ copyRun
  rintro ⟨t, pc⟩ post
  have pc' : pc = root + 284 := by
    simpa only [CopySite.next, Int64.ofBitVec_toBitVec] using post.returned.1
  subst pc
  have sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec := copy_stack args _ _ _ post
  have saved := copy_saved args _ _ _ post
  have rbx : t.regs.rbx = s.regs.rbx := saved.1
  have r12 : t.regs.r12 = s.regs.r12 := saved.2.2.1
  have rightPointer : t.regs.r15.toBitVec = source := by
    exact (congrArg UInt64.toBitVec saved.2.2.2.2.2).trans sourceReg
  have rightLength : t.regs.r14.toNat = input.size := by
    exact (congrArg UInt64.toNat saved.2.2.2.2.1).trans countReg
  have copiedCount : t.regs.rbp.toBitVec = BitVec.ofNat 64 count := by
    simpa only [args, bufferCopyArgs, selectedCount, UInt64.toBitVec_ofNat,
      bufferedReg, countReg, count] using congrArg UInt64.toBitVec saved.2.1
  have copiedCountNat : t.regs.rbp.toNat = count := by
    have small : count < 2 ^ 64 := by omega
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] using congrArg BitVec.toNat copiedCount
  let copied : Model := {counted with buffer :=
    copy state.buffer state.buffered.val input 0 count countBuffer (by omega)}
  have copiedState : StateAt t.dmem (s.regs.rsp.toBitVec + 8) copied :=
    copied_state args _ counted input 0 state.buffered.val count countBuffer (by omega)
      stored memory.statePhysical destination _ post
  have copyFrame : MemoryFrame s.dmem t.dmem (DrainWritable s.regs.rsp.toBitVec) := by
    apply copy_frame_drain args _ _ state.buffered.val
    · simp only [List.length_take, List.length_drop, Array.length_toList,
        ByteArray.size_data, Nat.sub_zero]
      omega
    · exact destination
    · exact post
  have oldLoad : Mem.loadInt t.dmem (t.regs.rsp.toBitVec + 104) 8 =
      some (Int.ofBytes (wordBytes (BitVec.ofNat 64 state.buffered.val))) := by
    apply state_buffered_word t copied
    simpa only [sp] using copiedState
  apply add_occupancy_runs e root hc.combine t (BitVec.ofNat 64 state.buffered.val) oldLoad
  intro sumFlags
  let u := occupancyAdded t (BitVec.ofNat 64 state.buffered.val) sumFlags
  have sumWord : BitVec.ofNat 64 state.buffered.val + t.regs.rbp.toBitVec =
      BitVec.ofNat 64 (state.buffered.val + count) := by
    rw [copiedCount, BitVec.ofNat_add]
  have sumNat : u.regs.rax.toNat = state.buffered.val + count := by
    change (BitVec.ofNat 64 state.buffered.val + t.regs.rbp.toBitVec).toNat = _
    rw [sumWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have sumMemory : u.dmem = (storeWord t 104
      (BitVec.ofNat 64 (state.buffered.val + count))).dmem := by
    simp only [u, occupancyAdded, sumWord]
  have counterFrame : MemoryFrame t.dmem u.dmem
      (fun a => InSpan a (s.regs.rsp.toBitVec + 104) 8) := by
    rw [sumMemory]
    simpa only [storeWord, sp] using storeInt_frame t.dmem
      (t.regs.rsp.toBitVec + 104) 8 (BitVec.ofNat 64 (state.buffered.val + count)).toInt
  have counterWide : MemoryFrame t.dmem u.dmem (DrainWritable s.regs.rsp.toBitVec) := by
    rw [sumMemory]
    simpa only [sp] using storeWord_frame t 104
      (BitVec.ofNat 64 (state.buffered.val + count)) (by decide) (by decide)
  have frameU : MemoryFrame s.dmem u.dmem (DrainWritable s.regs.rsp.toBitVec) := by
    intro a outside
    exact (counterWide a outside).trans (copyFrame a outside)
  have mappingU : MappedPreserved s.dmem u.dmem := by
    intro p n hm
    rw [sumMemory]
    exact storeWord_mapping t _ _ p n (post.mapped p n hm)
  have memoryU : DrainMemory root u.dmem u.regs.rsp.toBitVec source input := by
    change DrainMemory root u.dmem t.regs.rsp.toBitVec source input
    rw [sp]
    exact DrainMemory.after root _ _ _ _ _ memory frameU mappingU
  have chainU : u.regs.r12.toBitVec = u.regs.rsp.toBitVec + 72 := by
    change t.regs.r12.toBitVec = t.regs.rsp.toBitVec + 72
    rw [r12, sp]
    exact chainReg
  apply buffer_complete_test_runs e root hc.combine u
  intro branchFlags
  let v : MachineData := {u with status := branchFlags}
  rw [sumNat]
  by_cases incomplete : state.buffered.val + count < 64
  · rw [if_pos incomplete]
    have stateFinal := stateAt_store_buffered t.dmem (s.regs.rsp.toBitVec + 8) copied
      ⟨state.buffered.val + count, incomplete⟩ memory.statePhysical copiedState
    have sameModel : (update state input).state =
        {copied with buffered := ⟨state.buffered.val + count, incomplete⟩} := by
      simp only [update, nonempty, ↓reduceDIte, count, incomplete, copied, counted]
    apply Eventually.done
    refine ⟨rfl, ?_, frameU, mappingU, sp, rbx, r12⟩
    rw [sameModel]
    have location : (s.regs.rsp.toBitVec + 8) + 96 = s.regs.rsp.toBitVec + 104 := by bv_omega
    simpa only [v, u, occupancyAdded, storeWord, sumWord, sp, location] using stateFinal
  · rw [if_neg incomplete]
    have fullRun := full_buffer_runs e root hc compress v t.dmem copied source input memoryU
      (by simpa only [v, u, occupancyAdded, sp] using copiedState)
      (by simpa only [v, u, occupancyAdded, sp] using counterFrame) chainU
      (by change t.regs.rbp.toNat ≤ t.regs.r14.toNat; rw [copiedCountNat, rightLength]; exact countSource)
    apply eventually_trans (step e) _ _ _ fullRun
    rintro ⟨z, zpc⟩ fullPost
    have pcFull : zpc = root + 331 := fullPost.pc
    subst zpc
    have spZ : z.regs.rsp.toBitVec = s.regs.rsp.toBitVec := fullPost.rsp.trans sp
    have rbxZ : z.regs.rbx = s.regs.rbx := fullPost.rbx.trans rbx
    have r12Z : z.regs.r12 = s.regs.r12 := fullPost.r12.trans r12
    let complete : Model := {copied with
      chaining := compressBuffer copied.chaining copied.buffer, buffered := ⟨0, by decide⟩}
    have chainZ : z.regs.r12.toBitVec = z.regs.rsp.toBitVec + 72 := by
      rw [r12Z, spZ]
      exact chainReg
    have sourceZ : z.regs.r15.toBitVec = source + BitVec.ofNat 64 count := by
      rw [fullPost.right]
      change t.regs.r15.toBitVec + t.regs.rbp.toBitVec = _
      rw [rightPointer, copiedCount]
    have countZ : z.regs.r14.toNat = input.size - count := by
      rw [fullPost.remaining]
      change t.regs.r14.toNat - t.regs.rbp.toNat = _
      rw [rightLength, copiedCountNat]
    have memoryZ : DrainMemory root z.dmem z.regs.rsp.toBitVec source input := by
      rw [fullPost.rsp]
      exact fullPost.memory
    have stateZ : StateAt z.dmem (z.regs.rsp.toBitVec + 8) complete := by
      rw [fullPost.rsp]
      exact fullPost.state
    have run := right_drain_entry_runs e root hc compress z complete source input count countSource
      memoryZ stateZ chainZ sourceZ countZ
    apply eventually_weaken (step e) _ _ _ _ run
    intro result finish
    apply right_post_update root s z state complete source input count countSource result finish
      spZ rbxZ r12Z
    · intro a outside
      exact (fullPost.frame a (by simpa only [v, u, occupancyAdded, sp] using outside)).trans
        (frameU a outside)
    · intro p n hm
      exact fullPost.mapping p n (mappingU p n hm)
    · simp only [update, nonempty, ↓reduceDIte, count, incomplete,
        complete, copied, counted, compressBuffer]

end SszX86.Hash.Combine

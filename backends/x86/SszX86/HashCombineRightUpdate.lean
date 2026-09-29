import SszX86.HashCombineBufferedUpdate

namespace SszX86.Hash.Combine
open SszNative.HashStream

theorem UpdatePost.prepend (root : Int64) (s t : MachineData) (state : Model)
    (input : ByteArray) (result : MachineState)
    (post : UpdatePost root t state input result)
    (sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec)
    (rbx : t.regs.rbx = s.regs.rbx) (r12 : t.regs.r12 = s.regs.r12)
    (frame : MemoryFrame s.dmem t.dmem (DrainWritable s.regs.rsp.toBitVec))
    (mapping : MappedPreserved s.dmem t.dmem) : UpdatePost root s state input result := by
  refine ⟨post.pc, ?_, ?_, ?_, post.rsp.trans sp,
    post.rbx.trans rbx, post.r12.trans r12⟩
  · simpa only [sp] using post.state
  · intro a outside
    exact (post.frame a (by simpa only [sp] using outside)).trans (frame a outside)
  · intro p n hm
    exact post.mapping p n (mapping p n hm)

/-- Actual PC239 through PC399 implements one full update of an arbitrary raw
right slice. Length addition wraps before either branch; both empty-input paths
execute their shipped calls and branches. -/
theorem right_update_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (compress : CompressionCorrect e root) (s : MachineData) (state : Model)
    (source : BitVec 64) (input : ByteArray)
    (memory : DrainMemory root s.dmem s.regs.rsp.toBitVec source input)
    (stored : StateAt s.dmem (s.regs.rsp.toBitVec + 8) state)
    (chainReg : s.regs.r12.toBitVec = s.regs.rsp.toBitVec + 72)
    (sourceReg : s.regs.r15.toBitVec = source)
    (countReg : s.regs.r14.toNat = input.size)
    (bufferedReg : s.regs.r13.toNat = state.buffered.val) :
    Eventually (step e) (UpdatePost root s state input) (s, root + 239) := by
  have countBits : s.regs.r14.toBitVec = BitVec.ofNat 64 input.size := by
    rw [← countReg]
    simpa only [BitVec.setWidth_eq] using (BitVec.ofNat_toNat s.regs.r14.toBitVec).symm
  apply add_right_length_runs e root hc.combine s state.byteLen.toBitVec (state_length_word s state stored)
  intro lengthFlags
  let u := lengthAdded s state.byteLen.toBitVec lengthFlags
  have stateU : StateAt u.dmem (u.regs.rsp.toBitVec + 8)
      {state with byteLen := state.byteLen + UInt64.ofNat input.size} := by
    have h := stateAt_store_byteLen s.dmem (s.regs.rsp.toBitVec + 8) state
      (state.byteLen + UInt64.ofNat input.size) memory.statePhysical stored
    have location : (s.regs.rsp.toBitVec + 8) + 104 = s.regs.rsp.toBitVec + 112 := by bv_omega
    simpa only [u, lengthAdded, storeWord, countBits, UInt64.toBitVec_add,
      UInt64.toBitVec_ofNat, location] using h
  have frameU : MemoryFrame s.dmem u.dmem (DrainWritable s.regs.rsp.toBitVec) :=
    storeWord_frame s 112 (state.byteLen.toBitVec + s.regs.r14.toBitVec) (by decide) (by decide)
  have mappingU : MappedPreserved s.dmem u.dmem :=
    storeWord_mapping s 112 (state.byteLen.toBitVec + s.regs.r14.toBitVec)
  have memoryU : DrainMemory root u.dmem u.regs.rsp.toBitVec source input :=
    DrainMemory.after root _ _ _ _ _ memory frameU mappingU
  apply buffer_nonempty_test_runs e root hc.combine u
  intro testFlags
  let t : MachineData := {u with status := testFlags}
  by_cases empty : state.buffered.val = 0
  · have zero : s.regs.r13.toBitVec = 0 := by
      apply BitVec.eq_of_toNat_eq
      change s.regs.r13.toNat = 0
      exact bufferedReg.trans empty
    simp only [u, lengthAdded, storeWord, zero, ↓reduceIte]
    have run := empty_right_runs e root hc compress t state source input memoryU stateU empty
      chainReg sourceReg countReg
    apply eventually_weaken (step e) _ _ _ _ run
    intro result post
    exact UpdatePost.prepend root s t state input result post rfl rfl rfl frameU mappingU
  · have nonzero : s.regs.r13.toBitVec ≠ 0 := by
      intro zero
      apply empty
      rw [← bufferedReg]
      exact congrArg BitVec.toNat zero
    simp only [u, lengthAdded, storeWord, nonzero, ↓reduceIte]
    have run := buffered_right_runs e root hc compress t state source input memoryU stateU empty
      chainReg sourceReg countReg bufferedReg
    apply eventually_weaken (step e) _ _ _ _ run
    intro result post
    exact UpdatePost.prepend root s t state input result post rfl rfl rfl frameU mappingU

end SszX86.Hash.Combine

import SszX86.HashCombineCopyMemory
import SszX86.HashCombineBodyMemory

namespace SszX86.Hash.Combine
open SszNative.HashStream

structure RightPost (root : Int64) (s : MachineData) (state : Model)
    (source : BitVec 64) (input : ByteArray) (start : Nat)
    (bound : start ≤ input.size) (t : MachineState) : Prop where
  pc : t.2 = root + 399
  state : StateAt t.1.dmem (s.regs.rsp.toBitVec + 8)
    (drain state.buffer state.chaining state.byteLen input start bound).state
  memory : DrainMemory root t.1.dmem s.regs.rsp.toBitVec source input
  frame : MemoryFrame s.dmem t.1.dmem (DrainWritable s.regs.rsp.toBitVec)
  mapping : MappedPreserved s.dmem t.1.dmem
  rsp : t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec
  rbx : t.1.regs.rbx = s.regs.rbx
  r12 : t.1.regs.r12 = s.regs.r12
  rbp : t.1.regs.rbp = s.regs.rbp
  r13 : t.1.regs.r13 = s.regs.r13
  buffered : t.1.regs.r14.toNat = (input.size - start) % 64

private theorem nat_register (bits : UInt64) (n : Nat) (value : bits.toNat = n) :
    bits.toBitVec = BitVec.ofNat 64 n := by
  rw [← value]
  simpa only [BitVec.setWidth_eq] using (BitVec.ofNat_toNat bits.toBitVec).symm

/-- The right residual is copied from the original right allocation and its
exact occupancy is stored before the finalizer setup. -/
theorem right_short_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (s : MachineData) (state : Model) (source : BitVec 64) (input : ByteArray)
    (start : Nat) (bound : start ≤ input.size)
    (memory : DrainMemory root s.dmem s.regs.rsp.toBitVec source input)
    (stored : StateAt s.dmem (s.regs.rsp.toBitVec + 8) state)
    (sourceReg : s.regs.r15.toBitVec = source + BitVec.ofNat 64 start)
    (countReg : s.regs.r14.toNat = input.size - start)
    (short : input.size - start < 64) :
    Eventually (step e) (RightPost root s state source input start bound) (s, root + 377) := by
  let args := rightCopyArgs s
  have sourceArg : args.regs.rsi.toBitVec = source + BitVec.ofNat 64 start := sourceReg
  have countArg : args.regs.rdx.toBitVec = BitVec.ofNat 64 (input.size - start) :=
    nat_register s.regs.r14 _ countReg
  have copyRun := copy_slice_runs e root hc .rightResidual args source input start 0
    (input.size - start) memory (by omega) (by omega) sourceArg (by
      simp only [args, rightCopyArgs, UInt64.toBitVec_ofBitVec, BitVec.add_zero]) countArg
  apply right_copy_args_runs e root hc.combine s
  apply eventually_trans (step e) _ _ _ copyRun
  rintro ⟨t, pc⟩ post
  have pc' : pc = root + 394 := by
    simpa only [CopySite.next, Int64.ofBitVec_toBitVec] using post.returned.1
  subst pc
  have sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec := copy_stack args _ _ _ post
  have saved := copy_saved args _ _ _ post
  have reg : t.regs.r14 = s.regs.r14 := saved.2.2.2.2.1
  have copied := copied_state args _ state input start 0 (input.size - start)
    (by omega) (by omega) stored memory.statePhysical (by
      simp only [args, rightCopyArgs, UInt64.toBitVec_ofBitVec, BitVec.add_zero]) _ post
  have countWord : t.regs.r14.toBitVec = BitVec.ofNat 64 (input.size - start) := by
    rw [reg]
    exact nat_register _ _ countReg
  let copiedModel : Model := {state with buffer := copy state.buffer 0 input start
    (input.size - start) (by omega) (by omega)}
  have storedCount := stateAt_store_buffered t.dmem (s.regs.rsp.toBitVec + 8)
    copiedModel ⟨input.size - start, short⟩ memory.statePhysical copied
  have countAddress : (s.regs.rsp.toBitVec + 8) + 96 = s.regs.rsp.toBitVec + 104 := by
    bv_omega
  have copiedFrame : MemoryFrame s.dmem t.dmem (DrainWritable s.regs.rsp.toBitVec) := by
    apply copy_frame_drain args _ _ 0
    · simp only [List.length_take, List.length_drop, Array.length_toList, ByteArray.size_data]
      omega
    · simp only [args, rightCopyArgs, UInt64.toBitVec_ofBitVec, BitVec.add_zero]
    · exact post
  have storeFrame : MemoryFrame t.dmem
      (storeWord t 104 t.regs.r14.toBitVec).dmem (DrainWritable s.regs.rsp.toBitVec) := by
    apply frame_mono _ _ _ _ (storeInt_frame _ _ _ _)
    intro a inside
    rcases inside with ⟨i, hi, equal⟩
    left
    refine ⟨96 + i, by omega, ?_⟩
    rw [equal, sp]
    bv_omega
  have frame : MemoryFrame s.dmem (storeWord t 104 t.regs.r14.toBitVec).dmem
      (DrainWritable s.regs.rsp.toBitVec) := by
    intro a outside
    exact (storeFrame a outside).trans (copiedFrame a outside)
  have mapping : MappedPreserved s.dmem (storeWord t 104 t.regs.r14.toBitVec).dmem := by
    intro p n h
    exact Large.mapped_store _ _ _ _ _ _ (post.mapped p n h)
  have stateFinal : StateAt (storeWord t 104 t.regs.r14.toBitVec).dmem
      (s.regs.rsp.toBitVec + 8)
      (drain state.buffer state.chaining state.byteLen input start bound).state := by
    rw [drain_short _ _ _ _ _ bound short]
    simpa only [storeWord, sp, countWord, countAddress, copiedModel] using storedCount
  apply right_residual_store_runs e root hc.combine t
  · have mapping := post.mapped _ _ memory.state
    have part := mapped_subrange _ _ 112 96 8 mapping (by decide)
    simpa only [sp, countAddress] using part
  · apply Eventually.done
    refine ⟨rfl, stateFinal,
      DrainMemory.after root s.dmem _ _ source input memory frame mapping,
      frame, mapping, sp, saved.1, saved.2.2.1, saved.2.1,
      saved.2.2.2.1, ?_⟩
    simpa only [storeWord, reg, countReg, Nat.mod_eq_of_lt short]

/-- The actual right direct loop terminates by decreasing its physical remaining
length, not by bounding the wrapped aggregate message count. -/
theorem right_drain_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (compress : CompressionCorrect e root) (s : MachineData) (state : Model)
    (source : BitVec 64) (input : ByteArray) (start : Nat) (bound : start ≤ input.size)
    (memory : DrainMemory root s.dmem s.regs.rsp.toBitVec source input)
    (stored : StateAt s.dmem (s.regs.rsp.toBitVec + 8) state)
    (chainReg : s.regs.r12.toBitVec = s.regs.rsp.toBitVec + 72)
    (sourceReg : s.regs.r15.toBitVec = source + BitVec.ofNat 64 start)
    (countReg : s.regs.r14.toNat = input.size - start) :
    Eventually (step e) (RightPost root s state source input start bound)
      (s, if 64 ≤ input.size - start then root + 352 else root + 377) := by
  by_cases full : 64 ≤ input.size - start
  · rw [if_pos full]
    apply right_body_runs e root hc compress s state source input start memory stored
      chainReg sourceReg (by omega)
    rintro ⟨t, pc⟩ post flags flags'
    let u : MachineData := {rightAdvanced t flags with status := flags'}
    let nextState : Model := {state with chaining := Ssz.Sha256.compress state.chaining input start}
    have saved := compression_saved (rightCompressionArgs s) _ _ _ _ post
    have sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec :=
      compression_stack (rightCompressionArgs s) _ _ _ _ post
    have spU : u.regs.rsp.toBitVec = s.regs.rsp.toBitVec := sp
    have rbx : u.regs.rbx = s.regs.rbx := saved.1
    have r12 : u.regs.r12 = s.regs.r12 := saved.2.2.1
    have rbp : u.regs.rbp = s.regs.rbp := saved.2.1
    have r13 : u.regs.r13 = s.regs.r13 := saved.2.2.2.1
    have r14 : t.regs.r14 = s.regs.r14 := saved.2.2.2.2.1
    have r15 : t.regs.r15 = s.regs.r15 := saved.2.2.2.2.2
    have countU : u.regs.r14.toNat = input.size - (start + 64) := by
      change (t.regs.r14.toBitVec - 64).toNat = _
      rw [r14]
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reduceMod]
      change (2 ^ 64 - 64 + s.regs.r14.toNat) % 2 ^ 64 = _
      have limit := s.regs.r14.toBitVec.isLt
      omega
    have sourceU : u.regs.r15.toBitVec = source + BitVec.ofNat 64 (start + 64) := by
      change t.regs.r15.toBitVec + 64 = _
      rw [r15, sourceReg]
      rw [← memmove_addr_add]
    have chainU : u.regs.r12.toBitVec = u.regs.rsp.toBitVec + 72 := by
      rw [r12, spU]
      exact chainReg
    have memoryU : DrainMemory root u.dmem u.regs.rsp.toBitVec source input :=
      compressed_memory root (rightCompressionArgs s) source input _ _ _ _ memory chainReg post
    have stateU : StateAt u.dmem (u.regs.rsp.toBitVec + 8) nextState := by
      rw [spU]
      have h := compressed_state (rightCompressionArgs s) state _ _ _ stored
        memory.statePhysical chainReg memory.stackState post
      simpa only [inputBlock_compress, nextState] using h
    have frameU : MemoryFrame s.dmem u.dmem (DrainWritable s.regs.rsp.toBitVec) :=
      compression_frame_drain (rightCompressionArgs s) _ _ _ _ chainReg post
    have run := right_drain_runs e root hc compress u nextState source input (start + 64)
      (by omega) memoryU stateU chainU sourceU countU
    change Eventually (step e) _ (u, if 64 ≤ u.regs.r14.toNat then root + 352 else root + 377)
    rw [countU]
    apply eventually_weaken (step e) _ _ _ _ run
    intro result finish
    have same : (drain state.buffer state.chaining state.byteLen input start bound).state =
        (drain nextState.buffer nextState.chaining nextState.byteLen input (start + 64)
          (by omega)).state :=
      drain_step state.buffer state.chaining state.byteLen input start bound (by omega)
    refine ⟨finish.pc, ?_, ?_, ?_, ?_, finish.rsp.trans spU,
      finish.rbx.trans rbx, finish.r12.trans r12, finish.rbp.trans rbp,
      finish.r13.trans r13, ?_⟩
    · rw [same]
      simpa only [spU] using finish.state
    · simpa only [spU] using finish.memory
    · intro a outside
      have framed := finish.frame a (by simpa only [spU] using outside)
      exact framed.trans (frameU a outside)
    · intro p n hm
      exact finish.mapping p n (post.mapped p n hm)
    · rw [finish.buffered]
      omega
  · rw [if_neg full]
    exact right_short_runs e root hc s state source input start bound memory stored sourceReg
      countReg (by omega)
termination_by input.size - start
decreasing_by omega

end SszX86.Hash.Combine

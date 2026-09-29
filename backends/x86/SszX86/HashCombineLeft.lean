import SszX86.HashCombineCopyMemory
import SszX86.HashCombineBodyMemory

namespace SszX86.Hash.Combine
open SszNative.HashStream

structure LeftPost (root : Int64) (s : MachineData) (state : Model)
    (source : BitVec 64) (input : ByteArray) (start : Nat)
    (bound : start ≤ input.size) (t : MachineState) : Prop where
  pc : t.2 = root + 239
  state : StateAt t.1.dmem (s.regs.rsp.toBitVec + 8)
    (drain state.buffer state.chaining state.byteLen input start bound).state
  memory : DrainMemory root t.1.dmem s.regs.rsp.toBitVec source input
  frame : MemoryFrame s.dmem t.1.dmem (DrainWritable s.regs.rsp.toBitVec)
  mapping : MappedPreserved s.dmem t.1.dmem
  rsp : t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec
  rbx : t.1.regs.rbx = s.regs.rbx
  r12 : t.1.regs.r12 = s.regs.r12
  r14 : t.1.regs.r14 = s.regs.r14
  r15 : t.1.regs.r15 = s.regs.r15
  buffered : t.1.regs.r13.toNat = (input.size - start) % 64

private theorem nat_register (bits : UInt64) (n : Nat) (value : bits.toNat = n) :
    bits.toBitVec = BitVec.ofNat 64 n := by
  rw [← value]
  simpa only [BitVec.setWidth_eq] using (BitVec.ofNat_toNat bits.toBitVec).symm

/-- The left residual calls real memcpy even for zero bytes, records occupancy,
and stops only after the stored 112-byte state equals the exact drain result. -/
theorem left_short_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (s : MachineData) (state : Model) (source : BitVec 64) (input : ByteArray)
    (start : Nat) (bound : start ≤ input.size)
    (memory : DrainMemory root s.dmem s.regs.rsp.toBitVec source input)
    (stored : StateAt s.dmem (s.regs.rsp.toBitVec + 8) state)
    (sourceReg : s.regs.rbp.toBitVec = source + BitVec.ofNat 64 start)
    (countReg : s.regs.r13.toNat = input.size - start)
    (short : input.size - start < 64) :
    Eventually (step e) (LeftPost root s state source input start bound) (s, root + 217) := by
  let args := leftCopyArgs s
  have sourceArg : args.regs.rsi.toBitVec = source + BitVec.ofNat 64 start := sourceReg
  have countArg : args.regs.rdx.toBitVec = BitVec.ofNat 64 (input.size - start) :=
    nat_register s.regs.r13 _ countReg
  have copyRun := copy_slice_runs e root hc .leftResidual args source input start 0
    (input.size - start) memory (by omega) (by omega) sourceArg (by
      simp only [args, leftCopyArgs, UInt64.toBitVec_ofBitVec, BitVec.add_zero]) countArg
  apply left_copy_args_runs e root hc.combine s
  apply eventually_trans (step e) _ _ _ copyRun
  rintro ⟨t, pc⟩ post
  have pc' : pc = root + 234 := by
    simpa only [CopySite.next, Int64.ofBitVec_toBitVec] using post.returned.1
  subst pc
  have sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec := copy_stack args _ _ _ post
  have saved := copy_saved args _ _ _ post
  have reg : t.regs.r13 = s.regs.r13 := saved.2.2.2.1
  have copied := copied_state args _ state input start 0 (input.size - start)
    (by omega) (by omega) stored memory.statePhysical (by
      simp only [args, leftCopyArgs, UInt64.toBitVec_ofBitVec, BitVec.add_zero]) _ post
  have countWord : t.regs.r13.toBitVec = BitVec.ofNat 64 (input.size - start) := by
    rw [reg]
    exact nat_register _ _ countReg
  have physical := memory.statePhysical
  let copiedModel : Model := {state with buffer := copy state.buffer 0 input start
    (input.size - start) (by omega) (by omega)}
  have storedCount := stateAt_store_buffered t.dmem (s.regs.rsp.toBitVec + 8)
    copiedModel ⟨input.size - start, short⟩ physical copied
  have countAddress : (s.regs.rsp.toBitVec + 8) + 96 = s.regs.rsp.toBitVec + 104 := by
    bv_omega
  have copiedFrame : MemoryFrame s.dmem t.dmem (DrainWritable s.regs.rsp.toBitVec) := by
    apply copy_frame_drain args _ _ 0
    · simp only [List.length_take, List.length_drop, Array.length_toList, ByteArray.size_data]
      omega
    · simp only [args, leftCopyArgs, UInt64.toBitVec_ofBitVec, BitVec.add_zero]
    · exact post
  have storeFrame : MemoryFrame t.dmem
      (storeWord t 104 t.regs.r13.toBitVec).dmem (DrainWritable s.regs.rsp.toBitVec) := by
    apply frame_mono _ _ _ _ (storeInt_frame _ _ _ _)
    intro a inside
    rcases inside with ⟨i, hi, equal⟩
    left
    refine ⟨96 + i, by omega, ?_⟩
    rw [equal, sp]
    bv_omega
  have frame : MemoryFrame s.dmem (storeWord t 104 t.regs.r13.toBitVec).dmem
      (DrainWritable s.regs.rsp.toBitVec) := by
    intro a outside
    exact (storeFrame a outside).trans (copiedFrame a outside)
  have mapping : MappedPreserved s.dmem (storeWord t 104 t.regs.r13.toBitVec).dmem := by
    intro p n h
    exact Large.mapped_store _ _ _ _ _ _ (post.mapped p n h)
  have stateFinal : StateAt (storeWord t 104 t.regs.r13.toBitVec).dmem
      (s.regs.rsp.toBitVec + 8)
      (drain state.buffer state.chaining state.byteLen input start bound).state := by
    rw [drain_short _ _ _ _ _ bound short]
    simpa only [storeWord, sp, countWord, countAddress, copiedModel] using storedCount
  apply left_residual_store_runs e root hc.combine t
  · have mapping := post.mapped _ _ memory.state
    have part := mapped_subrange _ _ 112 96 8 mapping (by decide)
    simpa only [sp, countAddress] using part
  · apply Eventually.done
    refine ⟨rfl, stateFinal,
      DrainMemory.after root s.dmem _ _ source input memory frame mapping,
      frame, mapping, sp, saved.1, saved.2.2.1, saved.2.2.2.2.1,
      saved.2.2.2.2.2, ?_⟩
    simpa only [storeWord, reg, countReg, Nat.mod_eq_of_lt short]

/-- Induction follows the actual unsigned loop test. Each recursive call has
64 fewer physical bytes; the model recursion preserves every stale buffer byte. -/
theorem left_drain_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (compress : CompressionCorrect e root) (s : MachineData) (state : Model)
    (source : BitVec 64) (input : ByteArray) (start : Nat) (bound : start ≤ input.size)
    (memory : DrainMemory root s.dmem s.regs.rsp.toBitVec source input)
    (stored : StateAt s.dmem (s.regs.rsp.toBitVec + 8) state)
    (chainReg : s.regs.r12.toBitVec = s.regs.rsp.toBitVec + 72)
    (sourceReg : s.regs.rbp.toBitVec = source + BitVec.ofNat 64 start)
    (countReg : s.regs.r13.toNat = input.size - start) :
    Eventually (step e) (LeftPost root s state source input start bound)
      (s, if 64 ≤ input.size - start then root + 192 else root + 217) := by
  by_cases full : 64 ≤ input.size - start
  · rw [if_pos full]
    apply left_body_runs e root hc compress s state source input start memory stored
      chainReg sourceReg (by omega)
    rintro ⟨t, pc⟩ post flags flags'
    let u : MachineData := {leftAdvanced t flags with status := flags'}
    let nextState : Model := {state with chaining := Ssz.Sha256.compress state.chaining input start}
    have saved := compression_saved (leftCompressionArgs s) _ _ _ _ post
    have sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec :=
      compression_stack (leftCompressionArgs s) _ _ _ _ post
    have spU : u.regs.rsp.toBitVec = s.regs.rsp.toBitVec := sp
    have rbx : u.regs.rbx = s.regs.rbx := saved.1
    have r12 : u.regs.r12 = s.regs.r12 := saved.2.2.1
    have r14 : u.regs.r14 = s.regs.r14 := saved.2.2.2.2.1
    have r15 : u.regs.r15 = s.regs.r15 := saved.2.2.2.2.2
    have r13 : t.regs.r13 = s.regs.r13 := saved.2.2.2.1
    have rbp : t.regs.rbp = s.regs.rbp := saved.2.1
    have countU : u.regs.r13.toNat = input.size - (start + 64) := by
      change (t.regs.r13.toBitVec - 64).toNat = _
      rw [r13]
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reduceMod]
      change (2 ^ 64 - 64 + s.regs.r13.toNat) % 2 ^ 64 = _
      have limit := s.regs.r13.toBitVec.isLt
      omega
    have sourceU : u.regs.rbp.toBitVec = source + BitVec.ofNat 64 (start + 64) := by
      change t.regs.rbp.toBitVec + 64 = _
      rw [rbp, sourceReg]
      rw [← memmove_addr_add]
    have chainU : u.regs.r12.toBitVec = u.regs.rsp.toBitVec + 72 := by
      rw [r12, spU]
      exact chainReg
    have memoryU : DrainMemory root u.dmem u.regs.rsp.toBitVec source input :=
      compressed_memory root (leftCompressionArgs s) source input _ _ _ _ memory chainReg post
    have stateU : StateAt u.dmem (u.regs.rsp.toBitVec + 8) nextState := by
      rw [spU]
      have h := compressed_state (leftCompressionArgs s) state _ _ _ stored
        memory.statePhysical chainReg memory.stackState post
      simpa only [inputBlock_compress, nextState] using h
    have frameU : MemoryFrame s.dmem u.dmem (DrainWritable s.regs.rsp.toBitVec) :=
      compression_frame_drain (leftCompressionArgs s) _ _ _ _ chainReg post
    have run := left_drain_runs e root hc compress u nextState source input (start + 64)
      (by omega) memoryU stateU chainU sourceU countU
    change Eventually (step e) _ (u, if 64 ≤ u.regs.r13.toNat then root + 192 else root + 217)
    rw [countU]
    apply eventually_weaken (step e) _ _ _ _ run
    intro result finish
    have same : (drain state.buffer state.chaining state.byteLen input start bound).state =
        (drain nextState.buffer nextState.chaining nextState.byteLen input (start + 64)
          (by omega)).state :=
      drain_step state.buffer state.chaining state.byteLen input start bound (by omega)
    refine ⟨finish.pc, ?_, ?_, ?_, ?_, finish.rsp.trans spU,
      finish.rbx.trans rbx, finish.r12.trans r12, finish.r14.trans r14,
      finish.r15.trans r15, ?_⟩
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
    exact left_short_runs e root hc s state source input start bound memory stored sourceReg
      countReg (by omega)
termination_by input.size - start
decreasing_by omega

end SszX86.Hash.Combine

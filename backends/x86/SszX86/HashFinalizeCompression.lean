import SszX86.HashFinalizeZero
import SszX86.HashCompressionCall

namespace SszX86.Hash.Finalize
open SszNative.HashStream

/-- The finalizer's local frame and the CALL slot leave precisely 160 helper bytes. -/
theorem compression_pre (root : Int64) (entry : MachineData) (state : Model)
    (ra : BitVec 64) (pre : FinalizePre root entry state ra)
    (s : MachineData) (buf : Vector UInt8 64) (chain : Vector UInt32 8)
    (live : BufferPost root entry state ra buf chain s) :
    CompressionCallPre root (compressionSetup s) chain buf := by
  have rdi : (compressionSetup s).regs.rdi.toBitVec = entry.regs.rsi.toBitVec + 64 := by
    simp only [compressionSetup, get, UintCodec.Large.get, Reg64s.get64,
      UInt64.toBitVec_ofBitVec, live.regs.state]
  have rsi : (compressionSetup s).regs.rsi.toBitVec = entry.regs.rsi.toBitVec := by
    simp only [compressionSetup, live.regs.state]
  have rsp : (compressionSetup s).regs.rsp.toBitVec = entry.regs.rsp.toBitVec - 24 := live.regs.stack
  have bottom : (compressionSetup s).regs.rsp.toBitVec - 168 = entry.regs.rsp.toBitVec - 192 := by
    rw [rsp]
    bv_omega
  refine ⟨?_, ?_, live.memory.tables, ?_, ?_, pre.tablePhysical, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [compressionSetup, rdi] using live.chaining
  · simpa only [compressionSetup, rsi] using live.buffer
  · rw [rdi]
    have physical := pre.statePhysical
    unfold Physical at physical ⊢
    bv_omega
  · rw [rsi]
    have physical := pre.statePhysical
    unfold Physical at physical ⊢
    omega
  · rw [rsp]
    exact stack_subrange _ _ 192 24 168 live.memory.stack (by decide)
  · rw [rdi, rsi]
    intro i hi j hj equal
    have physical := pre.statePhysical
    unfold Physical at physical
    bv_omega
  · rw [bottom, rdi]
    intro i hi j hj equal
    apply pre.stackState i (by omega) (64 + j) (by omega)
    simpa only [memmove_addr_add] using equal
  · rw [bottom, rsi]
    intro i hi j hj
    exact pre.stackState i (by omega) j (by omega)
  · rw [rdi]
    constructor
    · simpa only [BitVec.add_zero] using disjoint_subrange _ _ 32 112 0 32 64 32
        pre.tablesState.1 (by decide) (by decide)
    · simpa only [BitVec.add_zero] using disjoint_subrange _ _ 256 112 0 256 64 32
        pre.tablesState.2 (by decide) (by decide)
  · rw [bottom]
    constructor
    · intro i hi j hj
      exact pre.tablesStack.1 i hi j (by omega)
    · intro i hi j hj
      exact pre.tablesStack.2 i hi j (by omega)

theorem compression_regs (entry s : MachineData) (live : RegsLive entry s)
    (ra : BitVec 64) (t : MachineState)
    (h : Returned (callState (compressionSetup s) ra) ra t) : RegsLive entry t.1 := by
  have saved := h.2.2
  refine ⟨saved.1.trans live.output, saved.2.2.2.2.1.trans live.state,
    ?_, saved.2.1.trans live.rbp, saved.2.2.1.trans live.r12,
    saved.2.2.2.1.trans live.r13, saved.2.2.2.2.2.trans live.r15⟩
  simpa only [callState, Emit.callState, compressionSetup, UInt64.toBitVec_ofBitVec,
    BitVec.sub_add_cancel, live.stack] using h.2.1

/-- Both real compression CALL sites consume the current physical block. -/
theorem compress_buffer_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (compress : CompressionCorrect e root)
    (entry : MachineData) (state : Model) (ra : BitVec 64)
    (pre : FinalizePre root entry state ra) (overflow : Bool)
    (s : MachineData) (buf : Vector UInt8 64) (chain : Vector UInt32 8)
    (live : BufferPost root entry state ra buf chain s) (P : MachineState → Prop)
    (next : ∀ t, BufferPost root entry state ra buf (compressBuffer chain buf) t →
      Eventually (step e) P (t, root - 256 + if overflow then 87 else 143)) :
    Eventually (step e) P (s, root - 256 + if overflow then 75 else 131) := by
  let prepared := compressionSetup s
  let ret := (root - 256 + if overflow then 87 else 143).toBitVec
  have prep := compression_pre root entry state ra pre s buf chain live
  have run := compression_helper_runs e root hc.compress compress prepared ret chain buf prep
  have slot : Mapped prepared.dmem (prepared.regs.rsp.toBitVec - 8) 8 :=
    zero_call_slot entry s live.regs live.memory.stack
  have resumed : Eventually (step e) P (callState prepared ret, root - 912) := by
    apply eventually_trans (step e) _ P _ run
    intro t post
    have statePtr : prepared.regs.rdi.toBitVec = entry.regs.rsi.toBitVec + 64 := by
      simp only [prepared, compressionSetup, get, UintCodec.Large.get, Reg64s.get64,
        UInt64.toBitVec_ofBitVec, live.regs.state]
    have bottom : prepared.regs.rsp.toBitVec - 168 = entry.regs.rsp.toBitVec - 192 := by
      change s.regs.rsp.toBitVec - 168 = _
      rw [live.regs.stack]
      bv_omega
    have frame : MemoryFrame s.dmem t.1.dmem (WorkWritable entry) := by
      apply frame_mono _ _ _ _ post.frame
      intro a inside
      rcases inside with inside | inside
      · apply state_store_work entry 64 32 (by decide) a
        simpa only [statePtr] using inside
      · exact Or.inr (Or.inr (by simpa only [bottom] using inside))
    have memory := memory_update root entry state ra pre s.dmem t.1.dmem live.memory frame post.mapped
    have regs := compression_regs entry s live.regs ret t post.returned
    have buffer : BytesAt t.1.dmem entry.regs.rsi.toBitVec buf.toList := by
      apply bytesAt_frame s.dmem t.1.dmem _ _ _ live.buffer post.frame
      intro i hi inside
      have hi' : i < 64 := by simpa using hi
      rcases inside with ⟨j, hj, equal⟩ | ⟨j, hj, equal⟩
      · have physical := pre.statePhysical
        unfold Physical at physical
        rw [statePtr] at equal
        bv_omega
      · rw [bottom] at equal
        exact pre.stackState j (by omega) i (by omega) equal.symm
    have chain' : ChainingAt t.1.dmem (entry.regs.rsi.toBitVec + 64)
        (compressBuffer chain buf) := by simpa only [statePtr] using post.state
    have finish := next t.1 ⟨memory, regs, buffer, chain'⟩
    simpa only [post.returned.1, ret, Int64.ofBitVec_toBitVec] using finish
  have target : root - 256 + Int64.ofInt (-656) = root - 912 := by
    apply Int64.toBitVec_inj.mp
    change root.toBitVec - 256 + BitVec.ofInt 64 (-656) = root.toBitVec - 912
    bv_omega
  cases overflow
  · apply final_compression_setup_runs e (root - 256) hc.finalize s P
    apply finalize_call138_cps e (root - 256) hc.finalize prepared P slot
    simpa only [ret, Bool.false_eq_true, ↓reduceIte, target] using resumed
  · apply overflow_compression_setup_runs e (root - 256) hc.finalize s P
    apply finalize_call82_cps e (root - 256) hc.finalize prepared P slot
    simpa only [ret, ↓reduceIte, target] using resumed

end SszX86.Hash.Finalize
